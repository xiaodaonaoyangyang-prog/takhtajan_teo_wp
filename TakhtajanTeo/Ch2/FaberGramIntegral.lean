import TakhtajanTeo.Ch2.FaberGram

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo.Ch2
open LiZhongQC

theorem normA21_congr_on {U : Set ℂ} (hU : MeasurableSet U) {f g : ℂ → ℂ}
    (he : EqOn f g U) : normA21 U f=normA21 U g := by
  unfold normA21
  congr 1
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem hU] with z hz
  rw [he hz]

theorem a21_congr_on {U : Set ℂ} (hU : MeasurableSet U) {f g : ℂ → ℂ}
    (hf : f∈A21fun U) (he : EqOn f g U) : g∈A21fun U := by
  refine ⟨hf.1.congr he.symm,?_⟩
  rw [← normA21_congr_on hU he]
  exact hf.2

theorem polynomial_mem_A21_bounded {U : Set ℂ} (hU : MeasurableSet U)
    {R : ℝ} (hR : U⊆closedBall (0 : ℂ) R) (p : Polynomial ℂ) :
    (fun z => p.eval z)∈A21fun U := by
  apply (mem_A21fun_iff_memLp hU).mpr
  refine ⟨p.differentiable.differentiableOn,?_⟩
  apply (memLp_two_iff_integrable_sq_norm p.continuous.aestronglyMeasurable).mpr
  exact ((by fun_prop : Continuous (fun z : ℂ => ‖p.eval z‖^2)).continuousOn.integrableOn_compact
    (isCompact_closedBall (0 : ℂ) R)).mono_set hR

/-- Exact complex-valued change of variables for a pair of holomorphic one-forms. -/
theorem faber_a21_pairing_pullback {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hi : InjOn f U) (ψ χ : ℂ → ℂ) :
    (∫ w in f '' U, ψ w*conj (χ w)) =
      ∫ z in U, (ψ (f z)*deriv f z)*conj (χ (f z)*deriv f z) := by
  rw [ahP_integral_image hU hf hi]
  apply setIntegral_congr_fun hU.measurableSet
  intro z _
  have hn : ((‖deriv f z‖^2 : ℝ) : ℂ)=deriv f z*conj (deriv f z) := by
    simp only [Complex.mul_conj,Complex.sq_norm]
  simp only [Complex.real_smul,map_mul,hn]
  ring

theorem normalized_pair_origin_ball {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g) :
    ∃ ε : ℝ, 0<ε ∧ ball (0 : ℂ) ε⊆f '' unitDisc := by
  have hopen := (RMT.differentiableOn_invFunOn_of_injOn isOpen_ball h.1 h.2.1).1
  have h0 : (0 : ℂ)∈f '' unitDisc := ⟨0,mem_ball_self one_pos,h.2.2.1⟩
  exact Metric.mem_nhds_iff.mp (hopen.mem_nhds h0)

theorem normalized_pair_bounded_disc_image {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g) :
    ∃ R : ℝ, f '' unitDisc⊆closedBall (0 : ℂ) R := by
  obtain ⟨φ,b,hφd,hφi,hφ0,hφ1,hb,hbg,hg⟩ := g1_inverted_exterior h
  have hopen := (RMT.differentiableOn_invFunOn_of_injOn isOpen_ball hφd hφi).1
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds
    (show (0 : ℂ)∈φ '' unitDisc from ⟨0,mem_ball_self one_pos,hφ0⟩))
  refine ⟨‖b‖/δ,?_⟩
  intro w hw
  apply mem_closedBall_zero_iff.mpr
  by_contra! hlarge
  have hwn : 0<‖w‖ := (div_nonneg (norm_nonneg b) hδ.le).trans_lt hlarge
  have hw0 : w≠0 := norm_pos_iff.mp hwn
  have hnear : b/w∈ball (0 : ℂ) δ := by
    apply mem_ball_zero_iff.mpr
    rw [norm_div]
    apply (div_lt_iff₀ hwn).mpr
    have hh := (div_lt_iff₀ hδ).mp hlarge
    nlinarith
  obtain ⟨s,hs,hφs⟩ := hball hnear
  have hs0 : s≠0 := by
    intro he
    have hbw : b/w≠0 := div_ne_zero hb hw0
    apply hbw
    simpa [he,hφ0] using hφs.symm
  have hgw : g s⁻¹=w := by
    have hh := hg s hs hs0
    rw [one_div,hφs] at hh
    rw [hh]
    field_simp
  exact Set.disjoint_left.mp h.2.2.2.2.2 hw ⟨s⁻¹,a21_inv_punctured ⟨hs,hs0⟩,hgw⟩

theorem normalized_pair_bounded_inverse_exterior {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g) :
    (∀ w∈g '' unitDiscExterior, w≠0) ∧
      ∃ R : ℝ, (fun w : ℂ => w⁻¹) '' (g '' unitDiscExterior)⊆closedBall (0 : ℂ) R := by
  obtain ⟨ε,hε,hball⟩ := normalized_pair_origin_ball h
  have hnorm (w : ℂ) (hw : w∈g '' unitDiscExterior) : ε≤‖w‖ := by
    by_contra! hh
    exact Set.disjoint_left.mp h.2.2.2.2.2 (hball (mem_ball_zero_iff.mpr hh)) hw
  have hne : ∀ w∈g '' unitDiscExterior, w≠0 := fun w hw => norm_pos_iff.mp (hε.trans_le (hnorm w hw))
  refine ⟨hne,ε⁻¹,?_⟩
  rintro _ ⟨w,hw,rfl⟩
  apply mem_closedBall_zero_iff.mpr
  rw [norm_inv]
  exact inv_anti₀ hε (hnorm w hw)

theorem polynomial_inverse_deriv_mem_A21 {U : Set ℂ} (hU : IsOpen U)
    (hne : ∀ w∈U, w≠0) {R : ℝ} (hR : (fun w : ℂ => w⁻¹) '' U⊆closedBall (0 : ℂ) R)
    (p : Polynomial ℂ) : (fun w => deriv (fun v => p.eval v⁻¹) w)∈A21fun U := by
  have hd : DifferentiableOn ℂ (fun w : ℂ => w⁻¹) U :=
    fun w hw => (differentiableAt_inv (hne w hw)).differentiableWithinAt
  have hi : InjOn (fun w : ℂ => w⁻¹) U := inv_injective.injOn
  have hV := (RMT.differentiableOn_invFunOn_of_injOn hU hd hi).1
  have hP := polynomial_mem_A21_bounded hV.measurableSet hR p.derivative
  have hconf : IsConformalOnto (fun w : ℂ => w⁻¹) U ((fun w : ℂ => w⁻¹) '' U) := ⟨hd,hi,rfl⟩
  apply a21_congr_on hU.measurableSet (a21_pullback hU hconf hP)
  intro w hw
  have he := deriv_comp w p.differentiableAt (differentiableAt_inv (hne w hw))
  convert he.symm using 1 <;> simp only [Function.comp_def,p.deriv]

def faberAlpha (P : ℕ → Polynomial ℂ) (n : ℕ) (w : ℂ) : ℂ :=
  (P (n+1)).derivative.eval w/(Real.sqrt (π*(n+1)) : ℂ)

def faberBeta (Q : ℕ → Polynomial ℂ) (n : ℕ) (w : ℂ) : ℂ :=
  deriv (fun v => (Q (n+1)).eval v⁻¹) w/(Real.sqrt (π*(n+1)) : ℂ)

theorem faberAlpha_mem_A21 {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    (P : ℕ → Polynomial ℂ) (n : ℕ) : faberAlpha P n∈A21fun (f '' unitDisc) := by
  have hD : IsOpen unitDisc := isOpen_ball
  have hopen := (RMT.differentiableOn_invFunOn_of_injOn hD h.1 h.2.1).1
  obtain ⟨R,hR⟩ := normalized_pair_bounded_disc_image h
  have hp := polynomial_mem_A21_bounded hopen.measurableSet hR (P (n+1)).derivative
  change (fun z => (P (n+1)).derivative.eval z/(Real.sqrt (π*(n+1)) : ℂ))∈A21fun (f '' unitDisc)
  simpa only [div_eq_mul_inv,mul_comm] using
    a21_const_mul hopen.measurableSet hp (Real.sqrt (π*(n+1)) : ℂ)⁻¹

theorem faberBeta_mem_A21 {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    (Q : ℕ → Polynomial ℂ) (n : ℕ) : faberBeta Q n∈A21fun (g '' unitDiscExterior) := by
  have hE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hopen := (RMT.differentiableOn_invFunOn_of_injOn hE h.2.2.2.2.1.1 h.2.2.2.2.1.2.1).1
  obtain ⟨hne,R,hR⟩ := normalized_pair_bounded_inverse_exterior h
  have hp := polynomial_inverse_deriv_mem_A21 hopen hne hR (Q (n+1))
  change (fun z => deriv (fun v => (Q (n+1)).eval v⁻¹) z/(Real.sqrt (π*(n+1)) : ℂ))∈A21fun (g '' unitDiscExterior)
  simpa only [div_eq_mul_inv,mul_comm] using
    a21_const_mul hopen.measurableSet hp (Real.sqrt (π*(n+1)) : ℂ)⁻¹

/-- The first actual image-domain Gram integral in Corollary 2.16. -/
theorem cor_2_16_gram_disc {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    {P Q : ℕ → Polynomial ℂ} (hPQ : IsFaber f g P Q) (m n : ℕ) :
    (∫ z in f '' unitDisc, (P (n+1)).derivative.eval z/Real.sqrt (π*(n+1))*
      conj ((P (m+1)).derivative.eval z/Real.sqrt (π*(m+1)))) =
      mulAdj (B3 (grunsky f g)) (B3 (grunsky f g)) n m := by
  change (∫ z in f '' unitDisc, faberAlpha P n z*conj (faberAlpha P m z))=_
  have hconf : IsConformalOnto f unitDisc (f '' unitDisc) := ⟨h.1,h.2.1,rfl⟩
  have hmem (i : ℕ) : (fun z => faberAlpha P i (f z)*deriv f z)∈A21fun unitDisc :=
    a21_pullback isOpen_ball hconf (faberAlpha_mem_A21 h P i)
  have hs (i : ℕ) : ∀ z∈unitDisc, HasSum (fun j => B3 (grunsky f g) i j*basisE j z)
      (faberAlpha P i (f z)*deriv f z) := by
    intro z hz
    convert faber_positive_pullback_basis h hPQ i hz using 1
    dsimp [faberAlpha]
    ring
  rw [faber_a21_pairing_pullback (show IsOpen unitDisc from isOpen_ball) h.1 h.2.1 (faberAlpha P n) (faberAlpha P m)]
  exact (A21_basis_pairing (hmem n) (hmem m) (hs n) (hs m)).tsum_eq.symm

/-- Transport an exterior Bergman expansion to the disk and remove the puncture
using genuine L2 membership, rather than assuming convergence at the origin. -/
theorem A21_exterior_expansion_to_disk {F : ℂ → ℂ} {x : ℕ → ℂ}
    (hF : F∈A21fun unitDiscExterior)
    (hs : ∀ z∈unitDiscExterior, HasSum (fun n => x n*basisF n z) (F z)) :
    ∃ H : ℂ → ℂ, H∈A21fun unitDisc ∧
      EqOn H (fun w => F w⁻¹*deriv (fun v : ℂ => v⁻¹) w) (unitDisc \ {0}) ∧
      ∀ w∈unitDisc, HasSum (fun n => (-x n)*basisE n w) (H w) := by
  have hU : IsOpen (unitDisc \ {(0 : ℂ)}) := isOpen_ball.sdiff isClosed_singleton
  obtain ⟨H,hH,hHeq,_⟩ := a21_remove_puncture (a21_pullback hU a21_inversion_conformal hF)
  let c : ℕ → ℂ := fun n => (-x n)*(Real.sqrt (((n : ℝ)+1)/π) : ℂ)
  have hnz (w : ℂ) (hw : w∈unitDisc) (hw0 : w≠0) : HasSum (fun n => c n*w^n) (H w) := by
    have hh := (hs w⁻¹ (a21_inv_punctured ⟨hw,hw0⟩)).mul_right (deriv (fun v : ℂ => v⁻¹) w)
    have hew : H w=F w⁻¹*deriv (fun v : ℂ => v⁻¹) w := hHeq ⟨hw,hw0⟩
    rw [← hew] at hh
    apply hh.congr_fun
    intro n
    have hp : (w⁻¹)^(-(n : ℤ)-2)=w^(n+2) := by
      rw [show -(n : ℤ)-2=-((n+2 : ℕ) : ℤ) by push_cast; ring,
        zpow_neg,zpow_natCast,inv_pow,inv_inv]
    simp only [c,basisF,deriv_inv,hp,pow_add]
    field_simp
    <;> ring
  have hser := g1_series_disk (d := c) (by
    intro r hr hr1
    refine ⟨(r : ℂ),by simp [abs_of_pos hr],?_⟩
    apply (hnz (r : ℂ) ?_ ?_).summable
    · simpa [unitDisc,abs_of_pos hr] using hr1
    · exact_mod_cast hr.ne')
  have hcl : unitDisc⊆closure (unitDisc \ {(0 : ℂ)}) := by
    have hd : Dense ({(0 : ℂ)}ᶜ : Set ℂ) := (finite_singleton (0 : ℂ)).countable.dense_compl ℝ
    intro w hw
    exact closure_mono (by intro z hz; exact ⟨hz.1,hz.2⟩)
      (hd.open_subset_closure_inter (show IsOpen unitDisc from isOpen_ball) hw)
  have heq : EqOn (fun w => ∑' n, c n*w^n) H unitDisc := by
    apply Set.EqOn.of_subset_closure (s := unitDisc \ {0}) (t := unitDisc) _ hser.2 hH.1.continuousOn diff_subset hcl
    intro w hw
    exact (hser.1 w hw.1).unique (hnz w hw.1 hw.2)
  refine ⟨H,hH,hHeq,?_⟩
  intro w hw
  have hh := hser.1 w hw
  have hew : (∑' n, c n*w^n)=H w := heq hw
  rw [hew] at hh
  apply hh.congr_fun
  intro n
  dsimp [c,basisE]
  ring

/-- Parseval pairing for the exterior Bergman basis, via L2 conformal inversion. -/
theorem A21_basisF_pairing {F G : ℂ → ℂ} {x y : ℕ → ℂ}
    (hF : F∈A21fun unitDiscExterior) (hG : G∈A21fun unitDiscExterior)
    (hx : ∀ z∈unitDiscExterior, HasSum (fun n => x n*basisF n z) (F z))
    (hy : ∀ z∈unitDiscExterior, HasSum (fun n => y n*basisF n z) (G z)) :
    HasSum (fun n => x n*conj (y n)) (∫ z in unitDiscExterior, F z*conj (G z)) := by
  obtain ⟨H,hH,hHe,hHs⟩ := A21_exterior_expansion_to_disk hF hx
  obtain ⟨J,hJ,hJe,hJs⟩ := A21_exterior_expansion_to_disk hG hy
  have hU : IsOpen (unitDisc \ {(0 : ℂ)}) := isOpen_ball.sdiff isClosed_singleton
  have hchange := faber_a21_pairing_pullback hU a21_inversion_conformal.1 a21_inversion_conformal.2.1 F G
  rw [a21_inversion_conformal.2.2] at hchange
  have hmeasure : volume.restrict (unitDisc \ {(0 : ℂ)})=volume.restrict unitDisc := by
    apply Measure.restrict_congr_set
    filter_upwards [volume.ae_ne (0 : ℂ)] with w hw
    simp [hw]
  have heq : (∫ z in unitDiscExterior, F z*conj (G z))=(∫ w in unitDisc, H w*conj (J w)) := by
    rw [hchange,hmeasure]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (show MeasurableSet unitDisc from measurableSet_ball),
      (volume.restrict unitDisc).ae_ne (0 : ℂ)] with w hw hw0
    rw [hHe ⟨hw,hw0⟩,hJe ⟨hw,hw0⟩]
  rw [heq]
  simpa only [map_neg,neg_mul,mul_neg,neg_neg] using A21_basis_pairing hH hJ hHs hJs

/-- The second actual image-domain Gram integral in Corollary 2.16. -/
theorem cor_2_16_gram_exterior {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    {P Q : ℕ → Polynomial ℂ} (hPQ : IsFaber f g P Q) (m n : ℕ) :
    (∫ z in g '' unitDiscExterior, deriv (fun w => (Q (n+1)).eval w⁻¹) z/Real.sqrt (π*(n+1))*
      conj (deriv (fun w => (Q (m+1)).eval w⁻¹) z/Real.sqrt (π*(m+1)))) =
      mulAdj (B2 (grunsky f g)) (B2 (grunsky f g)) n m := by
  change (∫ z in g '' unitDiscExterior, faberBeta Q n z*conj (faberBeta Q m z))=_
  have hE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hconf : IsConformalOnto g unitDiscExterior (g '' unitDiscExterior) :=
    ⟨h.2.2.2.2.1.1,h.2.2.2.2.1.2.1,rfl⟩
  have hmem (i : ℕ) : (fun z => faberBeta Q i (g z)*deriv g z)∈A21fun unitDiscExterior :=
    a21_pullback hE hconf (faberBeta_mem_A21 h Q i)
  have hs (i : ℕ) : ∀ z∈unitDiscExterior, HasSum (fun j => (-B2 (grunsky f g) i j)*basisF j z)
      (faberBeta Q i (g z)*deriv g z) := by
    intro z hz
    convert faber_negative_pullback_basis h hPQ i hz using 1
    dsimp [faberBeta]
    ring
  rw [faber_a21_pairing_pullback hE hconf.1 hconf.2.1]
  have hh := (A21_basisF_pairing (hmem n) (hmem m) (hs n) (hs m)).tsum_eq.symm
  simpa only [map_neg,neg_mul,mul_neg,neg_neg,mulAdj] using hh

end TakhtajanTeo.Ch2
