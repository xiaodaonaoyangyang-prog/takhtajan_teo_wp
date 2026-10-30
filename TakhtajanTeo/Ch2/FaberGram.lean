import TakhtajanTeo.Ch2.GrunskyOperator

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo.Ch2
open LiZhongQC

/-- Differentiate an actual disk power series and remove the zero derivative term. -/
theorem faber_powerSeries_deriv {F : ℂ → ℂ} {c : ℕ → ℂ}
    (hs : ∀ z∈unitDisc, HasSum (fun n => c n*z^n) (F z))
    {z : ℂ} (hz : z∈unitDisc) :
    HasSum (fun n => c (n+1)*((n+1 : ℕ) : ℂ)*z^n) (deriv F z) := by
  obtain ⟨R,hzR,hR1⟩ := exists_between (mem_ball_zero_iff.mp hz)
  have hR : 0<R := (norm_nonneg z).trans_lt hzR
  have hRD : (R : ℂ)∈unitDisc := by simpa [unitDisc,abs_of_pos hR] using hR1
  have hd := g2c_monomial_deriv (d := c) (k := id) hR (hs (R : ℂ) hRD).summable hzR
  simp only [id_eq] at hd
  have he : (fun u => ∑' n, c n*u^n)=ᶠ[𝓝 z] F := by
    filter_upwards [(isOpen_ball : IsOpen unitDisc).mem_nhds hz] with u hu
    exact (hs u hu).tsum_eq
  rw [he.deriv_eq] at hd
  simpa only [id_eq,Nat.add_sub_cancel,Finset.sum_range_one,Nat.cast_zero,mul_zero,zero_mul,sub_zero]
    using (hasSum_nat_add_iff' 1).mpr hd

/-- The differentiated positive Faber–Grunsky relation, before normalizing the basis. -/
theorem faber_positive_deriv_series {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    {P Q : ℕ → Polynomial ℂ} (hPQ : IsFaber f g P Q) (n : ℕ)
    {z : ℂ} (hz : z∈unitDisc) :
    HasSum (fun m : ℕ => ((n+1 : ℕ) : ℂ)*((m+1 : ℕ) : ℂ)*
      grunsky f g (n+1) (-(m+1 : ℤ))*z^m)
      ((P (n+1)).derivative.eval (f z)*deriv f z) := by
  let c : ℕ → ℂ := fun m => if m=0 then 0 else ((n+1 : ℕ) : ℂ)*grunsky f g (n+1) (-(m : ℤ))
  let F : ℂ → ℂ := fun w => (P (n+1)).eval (f w)-((n+1 : ℕ) : ℂ)*grunsky f g (n+1) 0
  have hs : ∀ w∈unitDisc, HasSum (fun m => c m*w^m) (F w) := by
    intro w hw
    have hh := (faber_grunsky h hPQ n).1 w hw
    have hshift : HasSum (fun m => c (m+1)*w^(m+1)) (F w) := by
      simpa only [c,F,show ∀ m : ℕ, ¬m+1=0 by omega,if_false,Nat.cast_add,Nat.cast_one] using hh
    simpa [c] using (hasSum_nat_add_iff (f := fun m => c m*w^m) 1).mp hshift
  have hd := faber_powerSeries_deriv hs hz
  have hfz := (h.1.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
  have hFd : HasDerivAt F ((P (n+1)).derivative.eval (f z)*deriv f z) z :=
    (((P (n+1)).hasDerivAt (f z)).comp z hfz).sub_const _
  rw [hFd.deriv] at hd
  apply hd.congr_fun
  intro m
  simp only [c,show ¬m+1=0 by omega,if_false,Nat.cast_add,Nat.cast_one]
  ring

theorem faber_gram_basis_weight (b : ℤ → ℤ → ℂ) (n m : ℕ) (z : ℂ) :
    B3 b n m*basisE m z =
      (((n+1 : ℕ) : ℂ)*((m+1 : ℕ) : ℂ)*b (n+1) (-(m+1 : ℤ))*z^m)/
        (Real.sqrt (π*(n+1)) : ℂ) := by
  have hn : 0<(n+1 : ℝ) := by positivity
  have hm : 0≤(m+1 : ℝ) := by positivity
  have hr : Real.sqrt (((n : ℝ)+1)*((m : ℝ)+1))*Real.sqrt (((m : ℝ)+1)/π) =
      ((n : ℝ)+1)*((m : ℝ)+1)/Real.sqrt (π*((n : ℝ)+1)) := by
    rw [Real.sqrt_mul hn.le,Real.sqrt_div hm,Real.sqrt_mul Real.pi_pos.le]
    have hsπ : Real.sqrt π≠0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
    have hsn : Real.sqrt ((n : ℝ)+1)≠0 := ne_of_gt (Real.sqrt_pos.mpr hn)
    calc
      _ = (Real.sqrt ((n : ℝ)+1)^2*Real.sqrt ((m : ℝ)+1)^2)/
          (Real.sqrt π*Real.sqrt ((n : ℝ)+1)) := by field_simp
      _ = _ := by rw [Real.sq_sqrt hn.le,Real.sq_sqrt hm]
  have hc : (Real.sqrt (((n : ℝ)+1)*((m : ℝ)+1)) : ℂ)*(Real.sqrt (((m : ℝ)+1)/π) : ℂ) =
      ((n+1 : ℕ) : ℂ)*((m+1 : ℕ) : ℂ)/(Real.sqrt (π*((n : ℝ)+1)) : ℂ) := by exact_mod_cast hr
  dsimp only [B3,basisE]
  push_cast
  calc
    _ = ((Real.sqrt (((n : ℝ)+1)*((m : ℝ)+1)) : ℂ)*(Real.sqrt (((m : ℝ)+1)/π) : ℂ))*
        b (n+1) (-(m+1 : ℤ))*z^m := by ring
    _ = _ := by rw [hc]; push_cast; ring

/-- The pullback coefficients entering the first Gram identity of Corollary 2.16.
This is a convergent pointwise series; it does not assert the Gram integral or completeness. -/
theorem faber_positive_pullback_basis {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    {P Q : ℕ → Polynomial ℂ} (hPQ : IsFaber f g P Q) (n : ℕ)
    {z : ℂ} (hz : z∈unitDisc) :
    HasSum (fun m : ℕ => B3 (grunsky f g) n m*basisE m z)
      (((P (n+1)).derivative.eval (f z)*deriv f z)/(Real.sqrt (π*(n+1)) : ℂ)) := by
  apply ((faber_positive_deriv_series h hPQ n hz).div_const (Real.sqrt (π*(n+1)) : ℂ)).congr_fun
  intro m
  exact faber_gram_basis_weight (grunsky f g) n m z

/-- Differentiate an exterior power series through inversion and its disk extension. -/
theorem faber_exteriorSeries_deriv {F : ℂ → ℂ} {c : ℕ → ℂ}
    (hs : ∀ z∈unitDiscExterior, HasSum (fun n : ℕ => c n*z^(-(n+1 : ℤ))) (F z))
    {z : ℂ} (hz : z∈unitDiscExterior) :
    HasSum (fun n : ℕ => -((n+1 : ℕ) : ℂ)*c n*z^(-(n+2 : ℤ))) (deriv F z) := by
  let G : ℂ → ℂ := fun w => if w=0 then 0 else F w⁻¹
  let d : ℕ → ℂ := fun n => if n=0 then 0 else c (n-1)
  have hD : ∀ w∈unitDisc, HasSum (fun n => d n*w^n) (G w) := by
    intro w hw
    by_cases hw0 : w=0
    · subst w
      rw [show G 0=0 by simp [G]]
      apply (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0).congr_fun
      intro n
      by_cases hn : n=0 <;> simp [d,hn]
    · have hS := hs w⁻¹ (a21_inv_punctured ⟨hw,hw0⟩)
      have hshift : HasSum (fun n => d (n+1)*w^(n+1)) (F w⁻¹) := by
        simpa only [d,Nat.add_sub_cancel,show ∀ n : ℕ, ¬n+1=0 by omega,if_false,
          g1_zpow_neg_succ,inv_inv] using hS
      simpa [d,G,hw0] using (hasSum_nat_add_iff (f := fun n => d n*w^n) 1).mp hshift
  have hzi := a21_inv_exterior hz
  have hz0 : z≠0 := norm_pos_iff.mp (zero_lt_one.trans hz)
  have hd := faber_powerSeries_deriv hD hzi.1
  have hGd : DifferentiableAt ℂ G z⁻¹ :=
    (differentiableOn_of_powerSeries hD).differentiableAt (isOpen_ball.mem_nhds hzi.1)
  have he : (fun w => G w⁻¹)=ᶠ[𝓝 z] F := by
    filter_upwards [eventually_ne_nhds hz0] with w hw
    simp [G,inv_ne_zero hw]
  have hFd := (hGd.hasDerivAt.comp z (hasDerivAt_inv hz0)).congr_of_eventuallyEq he.symm
  have hsum := hd.mul_right (-(z^2)⁻¹)
  rw [← hFd.deriv] at hsum
  apply hsum.congr_fun
  intro n
  have hp : z^(-(n+2 : ℤ))=(z^n*z^2)⁻¹ := by
    rw [zpow_neg,zpow_add₀ hz0,zpow_natCast]
    norm_num
  simp only [d,Nat.add_sub_cancel,show ¬n+1=0 by omega,if_false,hp,inv_pow,mul_inv_rev]
  ring

theorem faber_negative_deriv_series {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    {P Q : ℕ → Polynomial ℂ} (hPQ : IsFaber f g P Q) (n : ℕ)
    {z : ℂ} (hz : z∈unitDiscExterior) :
    HasSum (fun m : ℕ => -((n+1 : ℕ) : ℂ)*((m+1 : ℕ) : ℂ)*
      grunsky f g (m+1) (-(n+1 : ℤ))*z^(-(m+2 : ℤ)))
      (deriv (fun w => (Q (n+1)).eval w⁻¹) (g z)*deriv g z) := by
  let F : ℂ → ℂ := fun w => (Q (n+1)).eval (g w)⁻¹+((n+1 : ℕ) : ℂ)*grunsky f g (-(n+1 : ℤ)) 0
  have hs : ∀ w∈unitDiscExterior, HasSum
      (fun m : ℕ => (((n+1 : ℕ) : ℂ)*grunsky f g (m+1) (-(n+1 : ℤ)))*w^(-(m+1 : ℤ))) (F w) :=
    (faber_grunsky h hPQ n).2
  have hgz : g z≠0 := by
    intro he
    exact Set.disjoint_left.mp h.2.2.2.2.2 ⟨0,mem_ball_self one_pos,h.2.2.1⟩ ⟨z,hz,he⟩
  have hGd : DifferentiableAt ℂ (fun w => (Q (n+1)).eval w⁻¹) (g z) :=
    (Q (n+1)).differentiableAt.comp (g z) (differentiableAt_inv hgz)
  have hgd := (h.2.2.2.2.1.1.differentiableAt
    ((isOpen_lt continuous_const continuous_norm).mem_nhds hz)).hasDerivAt
  have hFd : HasDerivAt F (deriv (fun w => (Q (n+1)).eval w⁻¹) (g z)*deriv g z) z :=
    (hGd.hasDerivAt.comp z hgd).add_const _
  have hd := faber_exteriorSeries_deriv hs hz
  rw [hFd.deriv] at hd
  exact hd.congr_fun (fun m => by ring)

theorem faber_gram_exterior_basis_weight (b : ℤ → ℤ → ℂ) (n m : ℕ) (z : ℂ) :
    -B2 b n m*basisF m z =
      (-((n+1 : ℕ) : ℂ)*((m+1 : ℕ) : ℂ)*b (-(n+1 : ℤ)) (m+1)*z^(-(m+2 : ℤ)))/
        (Real.sqrt (π*(n+1)) : ℂ) := by
  have hh := faber_gram_basis_weight (fun i j => b (-i) (-j)) n m (1 : ℂ)
  have hc : B2 b n m*(Real.sqrt (((m : ℝ)+1)/π) : ℂ) =
      (((n+1 : ℕ) : ℂ)*((m+1 : ℕ) : ℂ)*b (-(n+1 : ℤ)) (m+1))/(Real.sqrt (π*(n+1)) : ℂ) := by
    simpa only [B2,B3,basisE,one_pow,mul_one,neg_neg] using hh
  simp only [basisF]
  rw [show -(m : ℤ)-2=-(m+2 : ℤ) by ring]
  calc
    _ = -(B2 b n m*(Real.sqrt (((m : ℝ)+1)/π) : ℂ))*z^(-(m+2 : ℤ)) := by ring
    _ = _ := by rw [hc]; ring

/-- The convergent exterior pullback coefficients entering the second Gram identity. -/
theorem faber_negative_pullback_basis {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    {P Q : ℕ → Polynomial ℂ} (hPQ : IsFaber f g P Q) (n : ℕ)
    {z : ℂ} (hz : z∈unitDiscExterior) :
    HasSum (fun m : ℕ => -B2 (grunsky f g) n m*basisF m z)
      ((deriv (fun w => (Q (n+1)).eval w⁻¹) (g z)*deriv g z)/(Real.sqrt (π*(n+1)) : ℂ)) := by
  apply ((faber_negative_deriv_series h hPQ n hz).div_const (Real.sqrt (π*(n+1)) : ℂ)).congr_fun
  intro m
  rw [faber_gram_exterior_basis_weight]
  have htranspose := (grunsky_spec h).1.2.2.2.2 (n+1) m
  simpa only [Nat.cast_add,Nat.cast_one] using congrArg
    (fun v : ℂ => (-((n+1 : ℕ) : ℂ)*((m+1 : ℕ) : ℂ)*v*z^(-(m+2 : ℤ)))/(Real.sqrt (π*(n+1)) : ℂ)) htranspose

end TakhtajanTeo.Ch2
