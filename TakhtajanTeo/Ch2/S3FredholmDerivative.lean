import TakhtajanTeo.Ch2.S3TraceCalculus
import TakhtajanTeo.Ch2.FaberBoundary
import Mathlib.Analysis.Calculus.SmoothSeries

/-! # Real Fréchet calculus for the Fredholm trace series -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real RightActions
noncomputable section
namespace TakhtajanTeo
open LiZhongQC
namespace Ch2

/-- Adjoint as an actual bounded real-linear map. -/
def s3fd_starOp : (ell2 →L[ℂ] ell2) →L[ℝ] (ell2 →L[ℂ] ell2) :=
  LinearMap.mkContinuous
    { toFun := star
      map_add' := fun T U => by exact star_add T U
      map_smul' := fun r T => by
        have hs (U : ell2 →L[ℂ] ell2) : r • U = (r : ℂ) • U := by
          ext x n
          simp only [ContinuousLinearMap.smul_apply,lp.coeFn_smul,Pi.smul_apply,Complex.real_smul,smul_eq_mul]
        change star (r • T) = r • star T
        rw [hs T,star_smul,hs (star T)]
        simp }
    1 (fun T => by
      change ‖ContinuousLinearMap.adjoint T‖ ≤ 1*‖T‖
      rw [LinearIsometryEquiv.norm_map,one_mul])

theorem s3fd_starOp_apply (T : ell2 →L[ℂ] ell2) : s3fd_starOp T = star T := rfl

def s3fd_gram (A : s3tc_HS) : ell2 →L[ℂ] ell2 := s3tc_toOperator A*star (s3tc_toOperator A)

def s3fd_gramChange (A D : s3tc_HS) : ell2 →L[ℂ] ell2 :=
  s3tc_toOperator A*star (s3tc_toOperator D) + s3tc_toOperator D*star (s3tc_toOperator A)

def s3fd_powerChange (A D : s3tc_HS) (N : ℕ) : ell2 →L[ℂ] ell2 :=
  ∑ j ∈ Finset.range N, (s3fd_gram A)^(N.pred-j)*s3fd_gramChange A D*(s3fd_gram A)^j

/-- Every finite trace-series summand, as a function on the real HS space. -/
def s3fd_coeff (N : ℕ) (A : s3tc_HS) : ℝ :=
  -(inner ℂ A (s3tc_left ((s3fd_gram A)^N) A)).re / (N+1)

theorem s3fd_gram_hasFDeriv (A : s3tc_HS) :
    ∃ L : s3tc_HS →L[ℝ] (ell2 →L[ℂ] ell2), HasFDerivAt s3fd_gram L A ∧
      ∀ D, L D = s3fd_gramChange A D := by
  have ho := s3tc_toOperator.hasFDerivAt.restrictScalars ℝ (x := A)
  have ha := s3fd_starOp.hasFDerivAt.comp A ho
  have hg := ho.fun_mul' ha
  refine ⟨_,hg,fun D => ?_⟩
  rfl

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in
theorem s3fd_power_hasFDeriv (A : s3tc_HS) (N : ℕ) :
    ∃ L : s3tc_HS →L[ℝ] (ell2 →L[ℂ] ell2), HasFDerivAt (fun X => s3fd_gram X^N) L A ∧
      ∀ D, L D = s3fd_powerChange A D N := by
  obtain ⟨L,hL,he⟩ := s3fd_gram_hasFDeriv A
  have hp := hL.fun_pow' N
  refine ⟨_,hp,fun D => ?_⟩
  change (∑ i ∈ Finset.range N,
    (s3fd_gram A^(N.pred-i) •> L <• s3fd_gram A^i : s3tc_HS →L[ℝ] (ell2 →L[ℂ] ell2))) D = _
  rw [show (∑ i ∈ Finset.range N,
    (s3fd_gram A^(N.pred-i) •> L <• s3fd_gram A^i : s3tc_HS →L[ℝ] (ell2 →L[ℂ] ell2))) D =
    ∑ i ∈ Finset.range N, (s3fd_gram A^(N.pred-i) •> L <• s3fd_gram A^i) D from
      sum_apply _ _ _]
  apply Finset.sum_congr rfl
  intro i hi
  change s3fd_gram A^(N.pred-i)*L D*s3fd_gram A^i = _
  rw [he]

theorem s3fd_coeff_hasFDeriv (A : s3tc_HS) (N : ℕ) :
    ∃ L : s3tc_HS →L[ℝ] ℝ, HasFDerivAt (s3fd_coeff N) L A ∧ ∀ D,
      L D = -((inner ℂ A (s3tc_left ((s3fd_gram A)^N) D + s3tc_left (s3fd_powerChange A D N) A)) +
        inner ℂ D (s3tc_left ((s3fd_gram A)^N) A)).re / (N+1) := by
  obtain ⟨L,hL,he⟩ := s3fd_power_hasFDeriv A N
  have hb := (s3tc_leftAction.isBoundedBilinearMap.hasFDerivAt ((s3fd_gram A)^N,A)).restrictScalars ℝ
  have hl := hb.comp (f := fun X : s3tc_HS => (s3fd_gram X^N,X)) A
    (hL.prodMk (hasFDerivAt_id A))
  have hi := (hasFDerivAt_id A).inner ℂ hl
  have hr := Complex.reCLM.hasFDerivAt.comp A hi
  have hf := hr.neg.mul_const (((N : ℝ)+1)⁻¹)
  refine ⟨_,(by simpa only [s3fd_coeff,div_eq_mul_inv] using! hf),?_⟩
  intro D
  simp only [smul_apply,smul_eq_mul,neg_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_restrictScalars',
    IsBoundedBilinearMap.deriv_apply,ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply,s3tc_leftAction_apply,he,fderivInnerCLM_apply,
    div_eq_mul_inv]
  ring
  rfl

theorem s3fd_star_norm (T : ell2 →L[ℂ] ell2) : ‖star T‖ = ‖T‖ := by
  change ‖ContinuousLinearMap.adjoint T‖ = _
  exact LinearIsometryEquiv.norm_map _ _

theorem s3fd_power_norm (A : s3tc_HS) {c : ℝ} (hc : 0 ≤ c)
    (hA : ‖s3tc_toOperator A‖ ≤ c) (N : ℕ) :
    ‖s3fd_gram A^N‖ ≤ (c^2)^N := by
  have hk : ‖s3fd_gram A‖ ≤ c^2 := by
    calc
      ‖s3fd_gram A‖ ≤ ‖s3tc_toOperator A‖ * ‖star (s3tc_toOperator A)‖ := norm_mul_le _ _
      _ ≤ c*c := by rw [s3fd_star_norm]; gcongr
      _ = c^2 := by ring
  induction N with
  | zero => simpa only [pow_zero] using! (ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := ell2))
  | succ n ih =>
    rw [pow_succ,pow_succ]
    exact (norm_mul_le _ _).trans (mul_le_mul ih hk (norm_nonneg _) (pow_nonneg (sq_nonneg c) n))

theorem s3fd_gramChange_norm (A D : s3tc_HS) {c : ℝ} (hc : 0 ≤ c)
    (hA : ‖s3tc_toOperator A‖ ≤ c) : ‖s3fd_gramChange A D‖ ≤ 2*c*‖D‖ := by
  have hd : ‖s3tc_toOperator D‖ ≤ ‖D‖ := s3tc_op_norm D
  calc
    ‖s3fd_gramChange A D‖ ≤
        ‖s3tc_toOperator A*star (s3tc_toOperator D)‖ +
        ‖s3tc_toOperator D*star (s3tc_toOperator A)‖ := norm_add_le _ _
    _ ≤ ‖s3tc_toOperator A‖*‖star (s3tc_toOperator D)‖ +
        ‖s3tc_toOperator D‖*‖star (s3tc_toOperator A)‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ c*‖D‖ + ‖D‖*c := by simp only [s3fd_star_norm]; gcongr
    _ = 2*c*‖D‖ := by ring

theorem s3fd_powerChange_norm (A D : s3tc_HS) {c : ℝ} (hc : 0 ≤ c)
    (hA : ‖s3tc_toOperator A‖ ≤ c) (N : ℕ) :
    ‖s3fd_powerChange A D N‖ ≤ (N : ℝ)*(c^2)^N.pred*(2*c*‖D‖) := by
  cases N with
  | zero => simp [s3fd_powerChange]
  | succ n =>
    have hp := s3fd_power_norm A hc hA
    have hd := s3fd_gramChange_norm A D hc hA
    calc
      ‖s3fd_powerChange A D (n+1)‖ ≤
          ∑ j ∈ Finset.range (n+1), ‖s3fd_gram A^(n-j)*s3fd_gramChange A D*s3fd_gram A^j‖ :=
        norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range (n+1), (c^2)^n*(2*c*‖D‖) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjn : n-j+j = n := Nat.sub_add_cancel (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hj))
        calc
          ‖s3fd_gram A^(n-j)*s3fd_gramChange A D*s3fd_gram A^j‖ ≤
              ‖s3fd_gram A^(n-j)‖*‖s3fd_gramChange A D‖*‖s3fd_gram A^j‖ :=
            (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
          _ ≤ (c^2)^(n-j)*(2*c*‖D‖)*(c^2)^j := by gcongr; exact hp _; exact hp _
          _ = (c^2)^n*(2*c*‖D‖) := by rw [mul_right_comm,← pow_add,hjn]
      _ = ((n+1 : ℕ) : ℝ)*(c^2)^(n+1 : ℕ).pred*(2*c*‖D‖) := by simp; ring

/-- A summable uniform derivative majorant; the predecessor convention includes N=0. -/
def s3fd_majorant (M c : ℝ) (N : ℕ) : ℝ :=
  2*M*(c^2)^N + 2*M^2*c*((N : ℝ)*(c^2)^N.pred)

theorem s3fd_majorant_summable (M : ℝ) {c : ℝ} (hc : 0 ≤ c) (hc1 : c < 1) :
    Summable (s3fd_majorant M c) := by
  have hr : ‖c^2‖ < 1 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg c)]
    nlinarith
  have h0 := summable_geometric_of_norm_lt_one hr
  have h1 : Summable (fun n : ℕ => (n : ℝ)*(c^2)^n) := by
    simpa only [pow_one] using summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have hp : Summable (fun n : ℕ => (n : ℝ)*(c^2)^n.pred) := by
    apply (summable_nat_add_iff 1).mp
    simpa [Nat.cast_add,Nat.cast_one,add_mul] using h1.add h0
  exact (h0.mul_left (2*M)).add (hp.mul_left (2*M^2*c))

theorem s3fd_coeff_differentiable (N : ℕ) : Differentiable ℝ (s3fd_coeff N) := by
  intro A
  obtain ⟨L,hL,-⟩ := s3fd_coeff_hasFDeriv A N
  exact hL.differentiableAt

/-- The operator norm of each actual Frechet derivative is bounded uniformly
on any HS-bounded set with an operator spectral gap. -/
theorem s3fd_coeff_fderiv_bound (A : s3tc_HS) {M c : ℝ} (hc : 0 ≤ c)
    (hA : ‖s3tc_toOperator A‖ ≤ c) (hM : ‖A‖ ≤ M) (N : ℕ) :
    ‖fderiv ℝ (s3fd_coeff N) A‖ ≤ s3fd_majorant M c N := by
  have hM0 : 0 ≤ M := (norm_nonneg A).trans hM
  obtain ⟨L,hL,he⟩ := s3fd_coeff_hasFDeriv A N
  rw [hL.fderiv]
  apply ContinuousLinearMap.opNorm_le_bound _ (by unfold s3fd_majorant; positivity)
  intro D
  rw [he]
  have hp := s3fd_power_norm A hc hA N
  have hd := s3fd_powerChange_norm A D hc hA N
  have hu : ‖s3tc_left (s3fd_gram A^N) D‖ ≤ (c^2)^N*‖D‖ :=
    (s3tc_left_norm _ _).trans (mul_le_mul_of_nonneg_right hp (norm_nonneg D))
  have hv : ‖s3tc_left (s3fd_powerChange A D N) A‖ ≤
      ((N : ℝ)*(c^2)^N.pred*(2*c*‖D‖))*M := by
    refine (s3tc_left_norm _ _).trans ?_
    gcongr
  have hw : ‖s3tc_left (s3fd_gram A^N) A‖ ≤ (c^2)^N*M := by
    refine (s3tc_left_norm _ _).trans ?_
    gcongr
  let Q := inner ℂ A (s3tc_left (s3fd_gram A^N) D + s3tc_left (s3fd_powerChange A D N) A) +
    inner ℂ D (s3tc_left (s3fd_gram A^N) A)
  change ‖-Q.re / ((N : ℝ)+1)‖ ≤ _
  have hden : 1 ≤ (N : ℝ)+1 := le_add_of_nonneg_left (Nat.cast_nonneg N)
  have hden0 : 0 ≤ (N : ℝ)+1 := by positivity
  calc
    ‖-Q.re / ((N : ℝ)+1)‖ = |Q.re| / ((N : ℝ)+1) := by
      simp only [norm_div,norm_neg,Real.norm_eq_abs,abs_of_nonneg hden0]
    _ ≤ |Q.re| := div_le_self (abs_nonneg _) hden
    _ ≤ ‖Q‖ := Complex.abs_re_le_norm Q
    _ ≤ ‖A‖*(‖s3tc_left (s3fd_gram A^N) D‖ + ‖s3tc_left (s3fd_powerChange A D N) A‖) +
        ‖D‖*‖s3tc_left (s3fd_gram A^N) A‖ := by
      exact (norm_add_le _ _).trans (add_le_add
        ((norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg A)))
        (norm_inner_le_norm _ _))
    _ ≤ M*((c^2)^N*‖D‖ + ((N : ℝ)*(c^2)^N.pred*(2*c*‖D‖))*M) +
        ‖D‖*((c^2)^N*M) := by gcongr
    _ = s3fd_majorant M c N*‖D‖ := by unfold s3fd_majorant; ring

/-- The genuine convergent real trace series on the operator unit ball. -/
def s3fd_logSeries (A : s3tc_HS) : ℝ := ∑' N, s3fd_coeff N A

theorem s3fd_coeff_summable (A : s3tc_HS) (hA : ‖s3tc_toOperator A‖ < 1) :
    Summable (fun N => s3fd_coeff N A) := by
  have h := (Complex.reCLM.summable (s3tc_gram_log_summable A hA)).neg
  have he (z : ℂ) (n : ℕ) : (z/((n : ℂ)+1)).re = z.re/((n : ℝ)+1) := by
    have hh : (n : ℂ)+1 = Complex.ofReal ((n : ℝ)+1) := by push_cast; rfl
    rw [hh,Complex.div_ofReal_re]
  simpa [s3fd_coeff,s3fd_gram,he,neg_div] using h

/-- The strict operator gap automatically persists on an actual HS ball. -/
theorem s3fd_local_bounds (A : s3tc_HS) (hA : ‖s3tc_toOperator A‖ < 1) :
    ∃ r > 0, ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ ∃ M : ℝ,
      ∀ X ∈ ball A r, ‖s3tc_toOperator X‖ ≤ c ∧ ‖X‖ ≤ M := by
  let r := (1-‖s3tc_toOperator A‖)/2
  let c := (‖s3tc_toOperator A‖+1)/2
  have hr : 0 < r := by dsimp [r]; linarith
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hc1 : c < 1 := by dsimp [c]; linarith
  refine ⟨r,hr,c,hc,hc1,‖A‖+1,fun X hX => ?_⟩
  have hx : ‖X-A‖ < r := mem_ball_iff_norm.mp hX
  have he : s3tc_toOperator X = s3tc_toOperator (X-A)+s3tc_toOperator A := by simp
  have ho : ‖s3tc_toOperator X‖ ≤ ‖X-A‖+‖s3tc_toOperator A‖ := by
    rw [he]
    have hd : ‖s3tc_toOperator (X-A)‖ ≤ ‖X-A‖ := s3tc_op_norm (X-A)
    exact (norm_add_le _ _).trans (add_le_add hd le_rfl)
  have hn : ‖X‖ ≤ ‖X-A‖+‖A‖ := by
    simpa only [sub_add_cancel] using norm_add_le (X-A) A
  constructor
  · dsimp [r] at hx
    dsimp [c]
    linarith
  · dsimp [r] at hx
    linarith [norm_nonneg (s3tc_toOperator A)]

/-- Genuine exchange of the full infinite trace sum and the Frechet derivative. -/
theorem s3fd_logSeries_hasFDeriv (A : s3tc_HS) (hA : ‖s3tc_toOperator A‖ < 1) :
    Summable (fun N => fderiv ℝ (s3fd_coeff N) A) ∧
      HasFDerivAt s3fd_logSeries (∑' N, fderiv ℝ (s3fd_coeff N) A) A := by
  obtain ⟨r,hr,c,hc,hc1,M,hb⟩ := s3fd_local_bounds A hA
  have hm := s3fd_majorant_summable M hc hc1
  have hself : A ∈ ball A r := mem_ball_self hr
  have hbound : ∀ N X, X ∈ ball A r →
      ‖fderiv ℝ (s3fd_coeff N) X‖ ≤ s3fd_majorant M c N := by
    intro N X hX
    exact s3fd_coeff_fderiv_bound X hc (hb X hX).1 (hb X hX).2 N
  refine ⟨Summable.of_norm_bounded hm (fun N => hbound N A hself),?_⟩
  exact hasFDerivAt_tsum_of_isPreconnected hm isOpen_ball (convex_ball A r).isPreconnected
    (fun N X _ => (s3fd_coeff_differentiable N X).hasFDerivAt) hbound hself
    (s3fd_coeff_summable A hA) hself

/-- Each term is the trace of products of two actual HS operators. -/
def s3fd_traceTerm (A D : s3tc_HS) (N : ℕ) : ℝ :=
  -(s3tc_trace (s3tc_left (s3fd_gram A^N) D + s3tc_left (s3fd_powerChange A D N) A)
      (s3tc_adjoint A) +
    s3tc_trace (s3tc_left (s3fd_gram A^N) A) (s3tc_adjoint D)).re / (N+1)

theorem s3fd_coeff_fderiv_apply (A D : s3tc_HS) (N : ℕ) :
    fderiv ℝ (s3fd_coeff N) A D = s3fd_traceTerm A D N := by
  obtain ⟨L,hL,he⟩ := s3fd_coeff_hasFDeriv A N
  rw [hL.fderiv,he]
  simp only [s3fd_traceTerm,s3tc_trace_gram_pair]

/-- Evaluation of the true Frechet derivative as an absolutely convergent trace series. -/
theorem s3fd_logSeries_trace (A D : s3tc_HS) (hA : ‖s3tc_toOperator A‖ < 1) :
    Summable (s3fd_traceTerm A D) ∧
      fderiv ℝ s3fd_logSeries A D = ∑' N, s3fd_traceTerm A D N := by
  obtain ⟨hs,hd⟩ := s3fd_logSeries_hasFDeriv A hA
  have he (N : ℕ) := s3fd_coeff_fderiv_apply A D N
  have hsum := (ContinuousLinearMap.apply ℝ ℝ D).summable hs
  refine ⟨by simpa only [ContinuousLinearMap.apply_apply,he] using hsum,?_⟩
  rw [hd.fderiv]
  have ht := (ContinuousLinearMap.apply ℝ ℝ D).map_tsum hs
  simpa only [ContinuousLinearMap.apply_apply,he] using ht

/-- Real-direction variation of the full trace series along any genuinely
HS-differentiable complex curve. -/
theorem s3fd_curve_derivative {F : ℂ → s3tc_HS} {d : s3tc_HS}
    (hF : HasDerivAt F d 0) (hgap : ‖s3tc_toOperator (F 0)‖ < 1) (v : ℂ) :
    HasDerivAt (fun s : ℝ => s3fd_logSeries (F ((s : ℂ)*v)))
      (∑' N, s3fd_traceTerm (F 0) (v • d) N) 0 := by
  have hline : HasDerivAt (fun s : ℝ => (s : ℂ)*v) v 0 := by
    simpa only [Complex.real_smul,id,Complex.ofReal_one,one_mul] using
      (hasDerivAt_id (0 : ℝ)).smul_const v
  have hR : HasDerivAt (fun s : ℝ => F ((s : ℂ)*v)) (v • d) 0 := by
    have h := (hF.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt_of_eq 0 hline (by simp)
    simpa only [Function.comp_def,ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearMap.toSpanSingleton_apply] using! h
  have hd := (s3fd_logSeries_hasFDeriv (F 0) hgap).2
  have h := hd.comp_hasDerivAt_of_eq 0 hR (by simp)
  have he := (s3fd_logSeries_trace (F 0) (v • d) hgap).2
  rw [hd.fderiv] at he
  exact h.congr_deriv he

/-- Compatibility with the actual quotient representative, using equality of
the welding pair on its domains rather than continuity of a selector. -/
theorem s3fd_grunsky_representative {ν : LinfStar} (hν : ν ∈ LinfStarBall) :
    grunsky (fsans ν) (gsans ν) =
      grunsky (fsans (Quotient.out (Phi ⟨ν,hν⟩) : LinfStarBall))
        (gsans (Quotient.out (Phi ⟨ν,hν⟩) : LinfStarBall)) := by
  apply FB.fb_grunsky_class hν (Quotient.out (Phi ⟨ν,hν⟩)).2
  exact Quotient.exact (Quotient.out_eq (Phi ⟨ν,hν⟩)).symm

/-- Identification with the installed Fredholm determinant, including the
valid Hilbert--Schmidt and quotient branches. -/
theorem s3fd_liouville_eq {ν : LinfStar} (hν : ν ∈ LinfStarBall) (A : s3tc_HS)
    (hentry : ∀ m n, A (m,n) = B1 (grunsky (fsans ν) (gsans ν)) m n) :
    s3fd_logSeries A = liouvilleS2 (Phi ⟨ν,hν⟩) := by
  let p := Phi ⟨ν,hν⟩
  let μ : LinfStar := (Quotient.out p : LinfStarBall)
  have hμ : μ ∈ LinfStarBall := (Quotient.out p).2
  have he (m n : ℕ) : A (m,n) = B1 (grunsky (fsans μ) (gsans μ)) m n := by
    rw [hentry,s3fd_grunsky_representative hν]
  have hp : p ∈ T01 := (cor_2_9 p).1.mpr ((s3tc_summable A).congr (fun q => by rw [he]))
  obtain ⟨lam,hl,-,-,-,-,-,hseries,-⟩ := s3fl_liouvilleS2_series hp
  obtain ⟨hr,hb⟩ := gop_grunsky_bounds (AppB.b8_welding_normalized_pair hμ) (r22_complement_null hμ)
    (B1 (grunsky (fsans μ) (gsans μ))) (Set.mem_insert _ _)
  obtain ⟨u,hu⟩ := gop_singular_basis hr hb hl
  have hop : s3tc_toOperator A = gopOp (B1 (grunsky (fsans μ) (gsans μ))) := by
    change gopOp (fun m n => A (m,n)) = _
    congr 1
    funext m n
    exact he m n
  have heig (n : ℕ) : (s3tc_toOperator A*star (s3tc_toOperator A)) (u n) =
      ((lam n^2 : ℝ) : ℂ) • u n := by
    rw [hop]
    exact hu n
  have hm (N : ℕ) : (inner ℂ A (s3tc_left (s3fd_gram A^N) A)).re =
      ∑' n, (lam n^2)^(N+1) := by
    obtain ⟨hs,ht⟩ := s3tc_gram_spectral A u lam heig N
    change (inner ℂ A (s3tc_left ((s3tc_toOperator A*star (s3tc_toOperator A))^N) A)).re = _
    rw [ht]
    simpa only [Complex.reCLM_apply,← Complex.ofReal_pow,Complex.ofReal_re] using
      Complex.reCLM.map_tsum hs
  have hs : s3fd_logSeries A = -(∑' N : ℕ, (∑' n, (lam n^2)^(N+1))/(N+1)) := by
    unfold s3fd_logSeries s3fd_coeff
    simp_rw [hm,neg_div]
    exact tsum_neg
  change s3fd_logSeries A = liouvilleS2 p
  rw [hs,← hseries,neg_neg]

/-- Actual Liouville S2 first variation in the original Bers coordinate.
The derivative is a convergent operator trace expression. Identification
with the Schwarzian kernel diagonal is a separate subsequent theorem. -/
theorem s3fd_chart_variation {ν : LinfStar} (hν : ν ∈ LinfStarBall)
    (hνT : Phi ⟨ν,hν⟩ ∈ T01) {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) :
    ∃ F : ℂ → s3tc_HS, ∃ d : s3tc_HS,
      (∀ᶠ t in 𝓝 (0 : ℂ), ∀ q : ℕ × ℕ, F t q =
        B1 (grunsky (fsans (beltramiMul (t • toLinf μ) ν))
          (gsans (beltramiMul (t • toLinf μ) ν))) q.1 q.2) ∧
      HasDerivAt F d 0 ∧ BersDiffAt liouvilleS2 ν μ ∧ ∀ v : ℂ,
        Summable (s3fd_traceTerm (F 0) (v • d)) ∧
        HasDerivAt (fun s : ℝ => liouvilleS2 (ptT (beltramiMul (((s : ℂ)*v) • toLinf μ) ν)))
          (∑' N, s3fd_traceTerm (F 0) (v • d) N) 0 := by
  let A : ℂ → ℕ → ℕ → ℂ := fun t => B1 (grunsky
    (fsans (beltramiMul (t • toLinf μ) ν)) (gsans (beltramiMul (t • toLinf μ) ν)))
  obtain ⟨D,-,hlim,-,r,hr,c,hc,hc1,hb⟩ := s3fv_chart_operator hν hνT hμ
  have hhs : ∀ᶠ t in 𝓝 (0 : ℂ), Summable (fun q : ℕ × ℕ => ‖A t q.1 q.2‖^2) := by
    filter_upwards [ball_mem_nhds (0 : ℂ) hr] with t ht
    exact (hb t ht).2.1
  obtain ⟨F,d,he,-,hF⟩ := s3fv_hilbert_derivative hhs hlim
  have hop : s3tc_toOperator (F 0) = gopOp (A 0) := by
    change gopOp (fun m n => F 0 (m,n)) = _
    congr 1
    funext m n
    exact he.self_of_nhds (m,n)
  have hgap : ‖s3tc_toOperator (F 0)‖ < 1 := by
    rw [hop]
    exact ((hb 0 (mem_ball_self hr)).2.2).trans_lt hc1
  have heq : (fun t => liouvilleS2 (ptT (beltramiMul (t • toLinf μ) ν))) =ᶠ[𝓝 (0 : ℂ)]
      (fun t => s3fd_logSeries (F t)) := by
    filter_upwards [he,ball_mem_nhds (0 : ℂ) hr] with t ht htr
    have hbt := (hb t htr).1
    rw [ptT,dif_pos hbt]
    exact (s3fd_liouville_eq hbt (F t) (fun m n => ht (m,n))).symm
  have hdiff : BersDiffAt liouvilleS2 ν μ := by
    apply DifferentiableAt.congr_of_eventuallyEq _ heq
    exact (s3fd_logSeries_hasFDeriv (F 0) hgap).2.differentiableAt.comp 0
      (hF.hasFDerivAt.restrictScalars ℝ).differentiableAt
  refine ⟨F,d,he,hF,hdiff,fun v => ⟨(s3fd_logSeries_trace (F 0) (v • d) hgap).1,?_⟩⟩
  apply (s3fd_curve_derivative hF hgap v).congr_of_eventuallyEq
  have ht : Tendsto (fun s : ℝ => (s : ℂ)*v) (𝓝 0) (𝓝 (0 : ℂ)) := by
    simpa using (Complex.continuous_ofReal.mul_const v).tendsto 0
  exact heq.comp_tendsto ht

/-- The real differentiability clause of Theorem 3.1, with only its original
base-point and harmonic tangent hypotheses. -/
theorem s3fd_bersDiffAt {p : T1} (hp : p ∈ T01) {μ : ℂ → ℂ}
    (hμ : μ ∈ harmonicL2 unitDiscExterior) :
    BersDiffAt liouvilleS2 (Quotient.out p : LinfStarBall) μ := by
  have hpt : Phi (Quotient.out p) ∈ T01 := by
    rw [show Phi (Quotient.out p) = p from Quotient.out_eq p]
    exact hp
  obtain ⟨F,d,he,hF,hd,-⟩ := s3fd_chart_variation (Quotient.out p).2 hpt hμ
  exact hd

/-- The complex Bers first variation, expressed by the two real-direction
operator trace series. No Schwarzian trace identification is assumed. -/
theorem s3fd_bersDz_trace {ν : LinfStar} (hν : ν ∈ LinfStarBall)
    (hνT : Phi ⟨ν,hν⟩ ∈ T01) {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) :
    ∃ A D : s3tc_HS,
      (∀ m n, A (m,n) = B1 (grunsky (fsans ν) (gsans ν)) m n) ∧
      Summable (s3fd_traceTerm A D) ∧ Summable (s3fd_traceTerm A (I • D)) ∧
      bersDz liouvilleS2 ν μ =
        ((∑' N, s3fd_traceTerm A D N : ℝ) -
          I * (∑' N, s3fd_traceTerm A (I • D) N : ℝ)) / 2 := by
  obtain ⟨F,d,he,hF,hd,hv⟩ := s3fd_chart_variation hν hνT hμ
  let f : ℂ → ℝ := fun t => liouvilleS2 (ptT (beltramiMul (t • toLinf μ) ν))
  have hf : DifferentiableAt ℝ f 0 := hd
  have heval (v : ℂ) : fderiv ℝ f 0 v = ∑' N, s3fd_traceTerm (F 0) (v • d) N := by
    have hline : HasDerivAt (fun s : ℝ => (s : ℂ)*v) v 0 := by
      simpa only [Complex.real_smul,id,Complex.ofReal_one,one_mul] using
        (hasDerivAt_id (0 : ℝ)).smul_const v
    have hh := hf.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
    exact hh.unique (hv v).2
  have hg := Complex.ofRealCLM.hasFDerivAt.comp 0 hf.hasFDerivAt
  refine ⟨F 0,d,?_,by simpa only [one_smul] using (hv 1).1,(hv I).1,?_⟩
  · intro m n
    simpa only [zero_smul,grp_zero_mul hν] using he.self_of_nhds (m,n)
  · change dz (Complex.ofRealCLM ∘ f) 0 = _
    rw [dz,hg.fderiv]
    simp only [ContinuousLinearMap.comp_apply,Complex.ofRealCLM_apply,heval,one_smul]

end Ch2
end TakhtajanTeo
