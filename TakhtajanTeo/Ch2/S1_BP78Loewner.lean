import TakhtajanTeo.Ch2.S1_BP78Completed
import TakhtajanTeo.Ch2.LoewnerChain
import TakhtajanTeo.Ch2.S1_BP78Explicit
import LiZhongQC.Lemmas.CaratheodoryJordan
import LiZhongQC.Ch02.S13_Representation
import LiZhongQC.Ch01.S08_Compactness

/-!
# Theorem 1.6 (iii) ⇒ (i) (Becker–Pommerenke [BP78] Satz 4), `ab16x_` helpers

The explicit Löwner chain `f_t(z) = f(e^{-t}z) + (e^t - e^{-t}) z f'(e^{-t}z)` (BP78 (1.8)) is a subordination
chain of univalent maps for small `t` (`ab16x_flow`, `ab16x_glue_injective`, via `Ch2/LoewnerChain`); its boundary
values give the extension `F(z) = f(1/z̄) + (z - 1/z̄) f'(1/z̄)` (`|z| > 1`), quasiconformal near `S¹` (`ab16x_qc`)
with dilatation `→ 0` (`ab16x_dilatation_tendsto`, in `Ch2/S1_BP78Explicit`).
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

namespace Ch2

/-- Carathéodory: `f` extends to a homeomorphism `f̂` of `𝔻̄` onto `cl f(𝔻)`. -/
theorem ab16x_caratheodory {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc)
    (hJ : IsJordanDomain (f '' unitDisc)) (hb : Bornology.IsBounded (f '' unitDisc)) :
    ∃ fh : ℂ → ℂ, ContinuousOn fh (closedBall (0 : ℂ) 1) ∧ InjOn fh (closedBall (0 : ℂ) 1) ∧
      EqOn fh f unitDisc := by
  have hconf : IsConformalOnto f unitDisc (f '' unitDisc) := ⟨hf, hinj, rfl⟩
  have hΩo : IsOpen (f '' unitDisc) := hJ.1
  have hJ' : IsJordanCurve (toExt (frontier (f '' unitDisc))) := by
    have := hJ.2.2
    rwa [frontier_toExt_of_isBounded' hb hΩo] at this
  obtain ⟨F, hFc, hFe, -, -⟩ := exists_continuousOn_extension_of_isJordanCurve_frontier hb hconf hJ'
  obtain ⟨G, hG1, hGc, hGi, -⟩ := caratheodory_jordan hb hconf hJ.2.2
  have hcl : closure (toExt unitDisc) = toExt (closedBall 0 1) := abN_closure_toExt_unitDisc
  have heq : EqOn (fun z : ℂ => ((F z : ℂ) : ExtPlane)) (fun z => G (z : ExtPlane))
      (closedBall (0 : ℂ) 1) := by
    refine Set.EqOn.of_subset_closure (s := unitDisc) (fun z hz => ?_) ?_ ?_ ball_subset_closedBall ?_
    · show ((F z : ℂ) : ExtPlane) = G (z : ExtPlane)
      rw [hFe hz, hG1 z hz]
    · exact OnePoint.continuous_coe.comp_continuousOn hFc
    · exact hGc.comp OnePoint.continuous_coe.continuousOn (fun z hz => by rw [hcl]; exact ⟨z, hz, rfl⟩)
    · rw [unitDisc, closure_ball (0 : ℂ) one_ne_zero]
  refine ⟨F, hFc, fun z₁ h₁ z₂ h₂ he => ?_, hFe⟩
  have h : ((F z₁ : ℂ) : ExtPlane) = ((F z₂ : ℂ) : ExtPlane) := by rw [he]
  have h' : G (z₁ : ExtPlane) = G (z₂ : ExtPlane) := (heq h₁).symm.trans (h.trans (heq h₂))
  exact OnePoint.coe_injective (hGi (by rw [hcl]; exact ⟨z₁, h₁, rfl⟩)
    (by rw [hcl]; exact ⟨z₂, h₂, rfl⟩) h')

/-- The chain tends to `f̂` uniformly on `𝔻̄` as `t → 0⁺`. -/
theorem ab16x_chain_tendsto {f fh : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc)
    (hfc : ContinuousOn fh (closedBall (0 : ℂ) 1)) (hfe : EqOn fh f unitDisc) :
    TendstoUniformlyOn (fun (t : ℝ) (z : ℂ) => f ((Real.exp (-t) : ℂ) * z) +
        ((Real.exp t : ℂ) - (Real.exp (-t) : ℂ)) * z * deriv f ((Real.exp (-t) : ℂ) * z))
      fh (𝓝[>] 0) (closedBall (0 : ℂ) 1) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hDc : IsCompact (closedBall (0 : ℂ) 1) := isCompact_closedBall _ _
  obtain ⟨κ, hκ, huc⟩ := Metric.uniformContinuousOn_iff.mp
    (hDc.uniformContinuousOn_of_continuous hfc) (ε / 20) (by positivity)
  have hθ : (0 : ℝ) < min 1 (κ / 2) := lt_min one_pos (by positivity)
  filter_upwards [Ioo_mem_nhdsGT hθ] with t ht z hz
  have ht0 : 0 < t := ht.1
  have ht1 : t < 1 := ht.2.trans_le (min_le_left _ _)
  have htκ : t < κ / 2 := ht.2.trans_le (min_le_right _ _)
  set e : ℝ := Real.exp (-t) with he
  have he0 : 0 < e := Real.exp_pos _
  have he1 : e < 1 := by
    calc e = Real.exp (-t) := he
      _ < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero
  have h1e : 1 - e ≤ t := by
    have := Real.add_one_le_exp (-t)
    linarith
  have hprod : Real.exp t * e = 1 := by rw [he, ← Real.exp_add]; simp
  have hz1 : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz
  set w : ℂ := (e : ℂ) * z with hw
  have hwn : ‖w‖ ≤ e := by
    rw [hw, norm_mul, Complex.norm_real, Real.norm_of_nonneg he0.le]
    nlinarith [norm_nonneg z]
  have hwD : w ∈ unitDisc := mem_ball_zero_iff.mpr (by linarith)
  have hwC : w ∈ closedBall (0 : ℂ) 1 := mem_closedBall_zero_iff.mpr (by linarith)
  -- `|f̂(z) - f(e^{-t}z)|` small
  have hA : ‖fh z - f w‖ < ε / 20 := by
    rw [← hfe hwD]
    have hd : dist z w < κ := by
      rw [dist_eq_norm]
      have : z - w = ((1 - e : ℝ) : ℂ) * z := by rw [hw]; push_cast; ring
      rw [this, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      nlinarith [norm_nonneg z]
    have := huc z hz w hwC hd
    rwa [dist_eq_norm] at this
  -- Cauchy estimate for `f'(w)` on the disc of radius `(1 - e)/2`
  set r : ℝ := (1 - e) / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have hball : closedBall w r ⊆ unitDisc := by
    intro ζ hζ
    rw [mem_closedBall, dist_eq_norm] at hζ
    refine mem_ball_zero_iff.mpr ?_
    calc ‖ζ‖ = ‖w + (ζ - w)‖ := by ring_nf
      _ ≤ ‖w‖ + ‖ζ - w‖ := norm_add_le _ _
      _ < 1 := by rw [hr] at hζ; linarith
  have hosc : ∀ ζ ∈ sphere w r, ‖f ζ - f w‖ ≤ ε / 20 := by
    intro ζ hζ
    have hζD := hball (sphere_subset_closedBall hζ)
    rw [← hfe hζD, ← hfe hwD]
    have hd : dist ζ w < κ := by rw [mem_sphere.mp hζ, hr]; linarith
    have := huc ζ (ball_subset_closedBall hζD) w hwC hd
    rw [dist_eq_norm] at this
    exact this.le
  have hder : ‖deriv f w‖ ≤ ε / 20 / r := by
    have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr0
      ((hf.sub_const (f w)).diffContOnCl_ball hball) hosc
    rwa [deriv_sub_const] at this
  -- the second term
  have hexp : Real.exp t < 3 := by
    have := Real.exp_one_lt_d9
    have : Real.exp t < Real.exp 1 := Real.exp_lt_exp.mpr ht1
    linarith
  have hfac : Real.exp t - e = Real.exp t * (1 - e) * (1 + e) := by linear_combination e * hprod
  have hpos : 0 ≤ Real.exp t - e := by
    rw [hfac]
    exact mul_nonneg (mul_nonneg (Real.exp_pos t).le (by linarith)) (by linarith)
  have h1e0 : (1 : ℝ) - e ≠ 0 := (by linarith : (0 : ℝ) < 1 - e).ne'
  have hB : ‖((Real.exp t : ℂ) - (e : ℂ)) * z * deriv f w‖ < 9 * ε / 10 := by
    have hc : ((Real.exp t : ℂ) - (e : ℂ)) = ((Real.exp t - e : ℝ) : ℂ) := by push_cast; ring
    rw [hc, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hpos]
    calc (Real.exp t - e) * ‖z‖ * ‖deriv f w‖ ≤ (Real.exp t - e) * 1 * (ε / 20 / r) := by
          gcongr
      _ = Real.exp t * (1 + e) * (ε / 10) := by
          rw [hfac, hr]; field_simp; ring
      _ < 9 * ε / 10 := by nlinarith
  rw [dist_eq_norm]
  have : fh z - (f w + ((Real.exp t : ℂ) - (e : ℂ)) * z * deriv f w) =
      (fh z - f w) - ((Real.exp t : ℂ) - (e : ℂ)) * z * deriv f w := by ring
  rw [this]
  calc ‖(fh z - f w) - ((Real.exp t : ℂ) - (e : ℂ)) * z * deriv f w‖
      ≤ ‖fh z - f w‖ + ‖((Real.exp t : ℂ) - (e : ℂ)) * z * deriv f w‖ := norm_sub_le _ _
    _ < ε / 20 + 9 * ε / 10 := add_lt_add hA hB
    _ < ε := by linarith

/-- `Re((1 + q)/(1 - q)) ≥ 1/3` for `|q| ≤ 1/2`. -/
theorem ab16x_re_bound {q : ℂ} (hq : ‖q‖ ≤ 1 / 2) : 1 / 3 ≤ ((1 + q) / (1 - q)).re := by
  have hq2 : q.re ^ 2 + q.im ^ 2 ≤ 1 / 4 := by
    have h := Complex.sq_norm q
    rw [Complex.normSq_apply] at h
    nlinarith [norm_nonneg q]
  have hx : q.re ≤ 1 / 2 := by nlinarith [sq_nonneg q.im, sq_nonneg (q.re - 1 / 2)]
  rw [Complex.div_re]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.sub_re, Complex.one_re, Complex.add_im,
    Complex.sub_im, Complex.one_im]
  rw [← add_div, le_div_iff₀ (by nlinarith)]
  nlinarith

/-- The glued extension at `|z| > 1` is the chain at time `log |z|`, evaluated at `z/|z|` (BP78 (1.3)). -/
theorem ab16x_glue_eq {f : ℂ → ℂ} {z : ℂ} (hz : 1 < ‖z‖) :
    f (conj z)⁻¹ + (z - (conj z)⁻¹) * deriv f (conj z)⁻¹ =
      f ((Real.exp (-(Real.log ‖z‖)) : ℂ) * (z / ‖z‖)) +
        ((Real.exp (Real.log ‖z‖) : ℂ) - (Real.exp (-(Real.log ‖z‖)) : ℂ)) * (z / ‖z‖) *
          deriv f ((Real.exp (-(Real.log ‖z‖)) : ℂ) * (z / ‖z‖)) := by
  have hn : 0 < ‖z‖ := by linarith
  have hz0 : z ≠ 0 := norm_pos_iff.mp hn
  have hn0 : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hinv : (conj z)⁻¹ = z / (‖z‖ : ℂ) ^ 2 := by
    rw [← Complex.mul_conj']
    have : conj z ≠ 0 := (map_ne_zero _).mpr hz0
    field_simp
  have hw : (Real.exp (-(Real.log ‖z‖)) : ℂ) * (z / ‖z‖) = (conj z)⁻¹ := by
    rw [Real.exp_neg, Real.exp_log hn, hinv]
    push_cast
    field_simp
  rw [hw, Real.exp_log hn, Real.exp_neg, Real.exp_log hn]
  congr 1
  rw [hinv]
  push_cast
  field_simp

/-- Margin for `q`: if `|q| ≤ 1/2` on `(0, α] × 𝔻̄`, then `|q| < 1` on `(a, b) × {|z| < e^{a/2}}`, `b ≤ α`. -/
theorem ab16x_q_margin {f : ℂ → ℂ} {α : ℝ}
    (hα : ∀ t ∈ Ioc 0 α, ∀ z ∈ closedBall (0 : ℂ) 1,
      ‖(1 - (Real.exp (-(2 * t)) : ℂ)) * ((Real.exp (-t) : ℂ) * z) *
        preSchwarzian f ((Real.exp (-t) : ℂ) * z)‖ ≤ 1 / 2)
    {a b : ℝ} (ha : 0 < a) (hb : b ≤ α) :
    ∀ τ ∈ Ioo a b, ∀ z ∈ ball (0 : ℂ) (Real.exp (a / 2)),
      ‖-(1 - (Real.exp (-(2 * τ)) : ℂ)) * ((Real.exp (-τ) : ℂ) * z) *
        preSchwarzian f ((Real.exp (-τ) : ℂ) * z)‖ < 1 := by
  intro τ hτ z hz
  have hτ0 : 0 < τ := ha.trans hτ.1
  rw [neg_mul, neg_mul, norm_neg]
  by_cases hz1 : ‖z‖ ≤ 1
  · exact lt_of_le_of_lt (hα τ ⟨hτ0, hτ.2.le.trans hb⟩ z (mem_closedBall_zero_iff.mpr hz1)) (by norm_num)
  rw [not_le] at hz1
  have hn : 0 < ‖z‖ := by linarith
  have hlog : Real.log ‖z‖ < a / 2 := by
    rw [Real.log_lt_iff_lt_exp hn]
    exact mem_ball_zero_iff.mp hz
  have hlog0 : 0 < Real.log ‖z‖ := Real.log_pos hz1
  set τ' : ℝ := τ - Real.log ‖z‖ with hτ'
  have hτ'0 : 0 < τ' := by rw [hτ']; linarith [hτ.1]
  have hτ'α : τ' ≤ α := by rw [hτ']; linarith [hτ.2]
  set ζ : ℂ := z / ‖z‖ with hζ
  have hζ1 : ‖ζ‖ = 1 := by
    rw [hζ, norm_div, Complex.norm_real, Real.norm_of_nonneg hn.le, div_self hn.ne']
  have hw : (Real.exp (-τ') : ℂ) * ζ = (Real.exp (-τ) : ℂ) * z := by
    rw [hτ', show -(τ - Real.log ‖z‖) = -τ + Real.log ‖z‖ by ring, Real.exp_add, Real.exp_log hn, hζ]
    have hn0 : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    push_cast
    field_simp
  have h' := hα τ' ⟨hτ'0, hτ'α⟩ ζ (mem_closedBall_zero_iff.mpr hζ1.le)
  rw [hw] at h'
  set N : ℝ := ‖((Real.exp (-τ) : ℂ) * z) * preSchwarzian f ((Real.exp (-τ) : ℂ) * z)‖ with hN
  have hc : ∀ u : ℝ, 0 ≤ 1 - Real.exp (-(2 * u)) → ‖(1 - (Real.exp (-(2 * u)) : ℂ))‖ = 1 - Real.exp (-(2 * u)) := by
    intro u hu
    rw [show (1 - (Real.exp (-(2 * u)) : ℂ)) = ((1 - Real.exp (-(2 * u)) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg hu]
  have hpos : ∀ u : ℝ, 0 < u → 0 < 1 - Real.exp (-(2 * u)) := fun u hu => by
    have : Real.exp (-(2 * u)) < 1 := by
      calc Real.exp (-(2 * u)) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
        _ = 1 := Real.exp_zero
    linarith
  rw [mul_assoc, norm_mul, hc τ' (hpos τ' hτ'0).le, ← hN] at h'
  rw [mul_assoc, norm_mul, hc τ (hpos τ hτ0).le, ← hN]
  have hN0 : 0 ≤ N := norm_nonneg _
  -- `1 - e^{-2τ} < 2 (1 - e^{-2τ'})` since `τ' ≥ τ/2`
  have hu : Real.exp (-(2 * τ')) ≤ Real.exp (-τ) := Real.exp_le_exp.mpr (by rw [hτ']; linarith [hτ.1])
  have he2 : Real.exp (-(2 * τ)) = Real.exp (-τ) ^ 2 := by rw [← Real.exp_nat_mul]; ring_nf
  have he1 : Real.exp (-τ) < 1 := by
    calc Real.exp (-τ) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero
  have hkey : 1 - Real.exp (-(2 * τ)) < 2 * (1 - Real.exp (-(2 * τ'))) := by
    rw [he2]
    nlinarith [Real.exp_pos (-τ)]
  rcases hN0.eq_or_lt with h0 | h0
  · rw [← h0, mul_zero]; norm_num
  nlinarith

/-- Regularity of the BP78 chain and of `q`: jointly `C¹` on `(a, b) × {|z| < ρ}`, holomorphic in `z`. -/
theorem ab16x_chain_regular {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc)
    {a b ρ : ℝ} (hρ : ρ ≤ Real.exp a) :
    ContDiffOn ℝ 1 (fun q : ℝ × ℂ => f ((Real.exp (-q.1) : ℂ) * q.2) +
        ((Real.exp q.1 : ℂ) - (Real.exp (-q.1) : ℂ)) * q.2 * deriv f ((Real.exp (-q.1) : ℂ) * q.2))
      (Ioo a b ×ˢ ball (0 : ℂ) ρ) ∧
    (∀ τ ∈ Ioo a b, DifferentiableOn ℂ (fun z => f ((Real.exp (-τ) : ℂ) * z) +
        ((Real.exp τ : ℂ) - (Real.exp (-τ) : ℂ)) * z * deriv f ((Real.exp (-τ) : ℂ) * z))
      (ball (0 : ℂ) ρ)) ∧
    ContDiffOn ℝ 1 (fun q : ℝ × ℂ => -(1 - (Real.exp (-(2 * q.1)) : ℂ)) * ((Real.exp (-q.1) : ℂ) * q.2) *
        preSchwarzian f ((Real.exp (-q.1) : ℂ) * q.2))
      (Ioo a b ×ˢ ball (0 : ℂ) ρ) := by
  have hU : IsOpen unitDisc := isOpen_ball
  have hmaps : ∀ τ, a < τ → ∀ z ∈ ball (0 : ℂ) ρ, (Real.exp (-τ) : ℂ) * z ∈ unitDisc := by
    intro τ hτ z hz
    refine mem_ball_zero_iff.mpr ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    have h1 : ‖z‖ < Real.exp a := (mem_ball_zero_iff.mp hz).trans_le hρ
    calc Real.exp (-τ) * ‖z‖ ≤ Real.exp (-τ) * Real.exp a := by gcongr
      _ = Real.exp (a - τ) := by rw [← Real.exp_add]; ring_nf
      _ < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero
  have hf1 : ContDiffOn ℝ 1 f unitDisc := (hf.contDiffOn hU).restrict_scalars ℝ
  have hdf : DifferentiableOn ℂ (deriv f) unitDisc := hf.deriv hU
  have hd1 : ContDiffOn ℝ 1 (deriv f) unitDisc := (hdf.contDiffOn hU).restrict_scalars ℝ
  have hPd : DifferentiableOn ℂ (preSchwarzian f) unitDisc := preSchwarzian_differentiableOn hU hf hinj
  have hP1 : ContDiffOn ℝ 1 (preSchwarzian f) unitDisc := (hPd.contDiffOn hU).restrict_scalars ℝ
  have hE : ∀ c : ℝ, ContDiff ℝ 1 (fun q : ℝ × ℂ => (Real.exp (c * q.1) : ℂ)) := fun c =>
    Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (contDiff_const.mul contDiff_fst))
  have hW : ContDiff ℝ 1 (fun q : ℝ × ℂ => (Real.exp (-q.1) : ℂ) * q.2) := by
    have := (hE (-1)).mul contDiff_snd
    simpa using this
  have hWm : MapsTo (fun q : ℝ × ℂ => (Real.exp (-q.1) : ℂ) * q.2) (Ioo a b ×ˢ ball (0 : ℂ) ρ) unitDisc :=
    fun q hq => hmaps q.1 hq.1.1 q.2 hq.2
  refine ⟨?_, ?_, ?_⟩
  · have h1 := hf1.comp hW.contDiffOn hWm
    have h2 := hd1.comp hW.contDiffOn hWm
    have hc : ContDiff ℝ 1 (fun q : ℝ × ℂ => ((Real.exp q.1 : ℂ) - (Real.exp (-q.1) : ℂ)) * q.2) := by
      have := ((hE 1).sub (hE (-1))).mul contDiff_snd
      simpa using this
    exact h1.add (hc.contDiffOn.mul h2)
  · intro τ hτ
    have hm : MapsTo (fun z : ℂ => (Real.exp (-τ) : ℂ) * z) (ball (0 : ℂ) ρ) unitDisc :=
      fun z hz => hmaps τ hτ.1 z hz
    have hl : DifferentiableOn ℂ (fun z : ℂ => (Real.exp (-τ) : ℂ) * z) (ball (0 : ℂ) ρ) :=
      (differentiable_id.const_mul _).differentiableOn
    exact (hf.comp hl hm).add (((differentiable_id.const_mul _).differentiableOn).mul (hdf.comp hl hm))
  · have h3 := hP1.comp hW.contDiffOn hWm
    have hc : ContDiff ℝ 1 (fun q : ℝ × ℂ => -(1 - (Real.exp (-(2 * q.1)) : ℂ))) := by
      have := ((contDiff_const (c := (1 : ℂ))).sub (hE (-2))).neg
      simpa using this
    exact (hc.mul hW).contDiffOn.mul h3

/-- The BP78 chain is a Löwner chain on `[s, t] ⊂ (0, α)`: `f_s = f_t ∘ φ` on `𝔻̄` (via `loew_flow_subordination`,
with `p = (1 + q)/(1 - q)`, `Re p ≥ 1/3`). -/
theorem ab16x_flow {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc)
    {C : ℝ → ℂ → ℂ} (hC : C = fun t z => f ((Real.exp (-t) : ℂ) * z) +
        ((Real.exp t : ℂ) - (Real.exp (-t) : ℂ)) * z * deriv f ((Real.exp (-t) : ℂ) * z))
    {α : ℝ} (hα : ∀ t ∈ Ioc 0 α, ∀ z ∈ closedBall (0 : ℂ) 1,
      ‖(1 - (Real.exp (-(2 * t)) : ℂ)) * ((Real.exp (-t) : ℂ) * z) *
        preSchwarzian f ((Real.exp (-t) : ℂ) * z)‖ ≤ 1 / 2)
    {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (htα : t < α) :
    ∃ φ : ℂ → ℂ, ContinuousOn φ (closedBall (0 : ℂ) 1) ∧ InjOn φ (closedBall (0 : ℂ) 1) ∧
      (∀ z ∈ closedBall (0 : ℂ) 1, ‖φ z‖ ≤ Real.exp (-(1 / 3 * (t - s))) * ‖z‖) ∧
      ∀ z ∈ closedBall (0 : ℂ) 1, C s z = C t (φ z) := by
  subst hC
  set a : ℝ := s / 2 with ha
  set b : ℝ := (t + α) / 2 with hb
  set ρ : ℝ := Real.exp (a / 2) with hρ
  have ha0 : 0 < a := by rw [ha]; linarith
  have hρ1 : 1 < ρ := by
    rw [hρ]
    calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
      _ < Real.exp (a / 2) := Real.exp_lt_exp.mpr (by linarith)
  have hreg := ab16x_chain_regular hf hinj (a := a) (b := b) (ρ := ρ) (Real.exp_le_exp.mpr (by linarith))
  have hmar := ab16x_q_margin hα (a := a) (b := b) ha0 (by rw [hb]; linarith)
  set Q : ℝ → ℂ → ℂ := fun τ z => -(1 - (Real.exp (-(2 * τ)) : ℂ)) * ((Real.exp (-τ) : ℂ) * z) *
      preSchwarzian f ((Real.exp (-τ) : ℂ) * z) with hQ
  have hQ1 : ∀ τ ∈ Ioo a b, ∀ z ∈ ball (0 : ℂ) ρ, 1 - Q τ z ≠ 0 := by
    intro τ hτ z hz h
    have : ‖Q τ z‖ < 1 := hmar τ hτ z hz
    rw [show Q τ z = 1 by linear_combination -h] at this
    simp at this
  have hQd : ContDiffOn ℝ 1 (fun q : ℝ × ℂ => Q q.1 q.2) (Ioo a b ×ˢ ball (0 : ℂ) ρ) := hreg.2.2
  have hp : ContDiffOn ℝ 1 (fun q : ℝ × ℂ => (1 + Q q.1 q.2) / (1 - Q q.1 q.2)) (Ioo a b ×ˢ ball (0 : ℂ) ρ) :=
    (((contDiffOn_const (c := (1 : ℂ))).add hQd).mul (((contDiffOn_const (c := (1 : ℂ))).sub hQd).inv
      (fun (q : ℝ × ℂ) (hq : q ∈ Ioo a b ×ˢ ball (0 : ℂ) ρ) => hQ1 q.1 hq.1 q.2 hq.2))).congr
      (fun q _ => div_eq_mul_inv _ _)
  have hpde : ∀ τ ∈ Ioo a b, ∀ z ∈ ball (0 : ℂ) ρ,
      HasDerivAt (fun σ => f ((Real.exp (-σ) : ℂ) * z) +
        ((Real.exp σ : ℂ) - (Real.exp (-σ) : ℂ)) * z * deriv f ((Real.exp (-σ) : ℂ) * z))
        (z * ((1 + Q τ z) / (1 - Q τ z)) * deriv (fun u => f ((Real.exp (-τ) : ℂ) * u) +
          ((Real.exp τ : ℂ) - (Real.exp (-τ) : ℂ)) * u * deriv f ((Real.exp (-τ) : ℂ) * u)) z) τ := by
    intro τ hτ z hz
    have hτ0 : 0 < τ := ha0.trans hτ.1
    have hz' : ‖z‖ < Real.exp τ := (mem_ball_zero_iff.mp hz).trans
      (Real.exp_lt_exp.mpr (by linarith [hτ.1]))
    obtain ⟨h1, h2⟩ := ab16x_chain_pde hf hinj hτ0 hz'
    have hne := hQ1 τ hτ z hz
    have key : ∀ A B c : ℂ, B ≠ 0 → z * (A / B) * (c * B) = z * (c * A) := by
      intro A B c hB
      field_simp
    convert h2 using 1
    rw [h1]
    exact key _ _ _ hne
  have hRe : ∀ τ ∈ Icc s t, ∀ z ∈ closedBall (0 : ℂ) 1, 1 / 3 ≤ ((1 + Q τ z) / (1 - Q τ z)).re := by
    intro τ hτ z hz
    apply ab16x_re_bound
    have := hα τ ⟨hs.trans_le hτ.1, hτ.2.trans htα.le⟩ z hz
    simp only [hQ, neg_mul, norm_neg]
    exact this
  exact loew_flow_subordination (f := fun t z => f ((Real.exp (-t) : ℂ) * z) +
      ((Real.exp t : ℂ) - (Real.exp (-t) : ℂ)) * z * deriv f ((Real.exp (-t) : ℂ) * z))
    (p := fun τ z => (1 + Q τ z) / (1 - Q τ z)) hst (by rw [ha]; linarith) (by rw [hb]; linarith)
    hρ1 (by norm_num) hreg.1 hreg.2.1 hp hpde hRe


/-- (BP78 (3.8), (1.3)) The glued map is a continuous injection of a closed disc `|z| ≤ e^τ`. -/
theorem ab16x_glue_injective {f fh : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc)
    (hA : Tendsto (fun z => ((1 - ‖z‖ ^ 2) : ℂ) * preSchwarzian f z)
      (comap (fun z : ℂ => ‖z‖) (𝓝[<] 1)) (𝓝 0))
    (hfc : ContinuousOn fh (closedBall (0 : ℂ) 1)) (hfi : InjOn fh (closedBall (0 : ℂ) 1))
    (hfe : EqOn fh f unitDisc) :
    ∃ τ > 0, ContinuousOn (fun z : ℂ => if ‖z‖ ≤ 1 then fh z else
        f (conj z)⁻¹ + (z - (conj z)⁻¹) * deriv f (conj z)⁻¹) (closedBall (0 : ℂ) (Real.exp τ)) ∧
      InjOn (fun z : ℂ => if ‖z‖ ≤ 1 then fh z else
        f (conj z)⁻¹ + (z - (conj z)⁻¹) * deriv f (conj z)⁻¹) (closedBall (0 : ℂ) (Real.exp τ)) := by
  obtain ⟨α, hα0, hα⟩ := ab16x_q_bound hf hinj hA
  set C : ℝ → ℂ → ℂ := fun t z => f ((Real.exp (-t) : ℂ) * z) +
    ((Real.exp t : ℂ) - (Real.exp (-t) : ℂ)) * z * deriv f ((Real.exp (-t) : ℂ) * z) with hC
  have hflow : ∀ s t : ℝ, 0 < s → s ≤ t → t < α → ∃ φ : ℂ → ℂ,
      ContinuousOn φ (closedBall (0 : ℂ) 1) ∧ InjOn φ (closedBall (0 : ℂ) 1) ∧
      (∀ z ∈ closedBall (0 : ℂ) 1, ‖φ z‖ ≤ Real.exp (-(1 / 3 * (t - s))) * ‖z‖) ∧
      ∀ z ∈ closedBall (0 : ℂ) 1, C s z = C t (φ z) :=
    fun s t hs hst ht => ab16x_flow hf hinj hC hα hs hst ht
  choose! Φ hΦc hΦi hΦb hΦe using hflow
  have hX4 : TendstoUniformlyOn C fh (𝓝[>] 0) (closedBall (0 : ℂ) 1) := ab16x_chain_tendsto hf hfc hfe
  have hD1 : ∀ z : ℂ, ‖z‖ ≤ 1 → z ∈ closedBall (0 : ℂ) 1 := fun z hz => mem_closedBall_zero_iff.mpr hz
  have hexp1 : ∀ u : ℝ, 0 < u → Real.exp (-u) < 1 := fun u hu => by
    calc Real.exp (-u) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero
  have hexp1' : ∀ u : ℝ, 0 < u → 1 < Real.exp u := fun u hu => by
    calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
      _ < Real.exp u := Real.exp_lt_exp.mpr hu
  -- holomorphy and continuity of `C t`
  have hCd : ∀ t : ℝ, 0 < t → t < α → DifferentiableOn ℂ (C t) (ball (0 : ℂ) (Real.exp (t / 4))) := by
    intro t ht htα
    exact (ab16x_chain_regular hf hinj (a := t / 2) (b := α) (ρ := Real.exp (t / 4))
      (Real.exp_le_exp.mpr (by linarith))).2.1 t ⟨by linarith, htα⟩
  -- small-time univalence (`loew_injOn_small_time` with `G = C (α/2)`)
  set α' : ℝ := α / 2 with hα'
  set τ₀ : ℝ := α / 4 with hτ₀
  set r₀ : ℝ := Real.exp (-(1 / 3 * (α' - τ₀))) with hr₀
  have hα'0 : 0 < α' := by rw [hα']; linarith
  have hτ₀0 : 0 < τ₀ := by rw [hτ₀]; linarith
  have hτ₀α' : τ₀ < α' := by rw [hτ₀, hα']; linarith
  have hα'α : α' < α := by rw [hα']; linarith
  have hr₀1 : r₀ < 1 := hexp1 _ (by nlinarith)
  have hr₀ρ : r₀ < Real.exp (α' / 4) := hr₀1.trans (hexp1' _ (by linarith))
  have hG' : ∀ w ∈ closedBall (0 : ℂ) r₀, deriv (C α') w ≠ 0 := by
    intro w hw
    have hw1 : ‖w‖ ≤ 1 := (mem_closedBall_zero_iff.mp hw).trans hr₀1.le
    have hw' : ‖w‖ < Real.exp α' := lt_of_le_of_lt hw1 (hexp1' _ hα'0)
    obtain ⟨h1, -⟩ := ab16x_chain_pde hf hinj hα'0 hw'
    simp only [hC]
    rw [h1]
    have hwD : (Real.exp (-α') : ℂ) * w ∈ unitDisc := ab16xe_mem hw'
    refine mul_ne_zero (mul_ne_zero (by exact_mod_cast (Real.exp_pos _).ne') ?_) ?_
    · exact deriv_ne_zero_of_injOn isOpen_ball hf hinj hwD
    · intro h0
      have hq := hα α' ⟨hα'0, hα'α.le⟩ w (hD1 w hw1)
      have hq1 : -(1 - (Real.exp (-(2 * α')) : ℂ)) * ((Real.exp (-α') : ℂ) * w) *
          preSchwarzian f ((Real.exp (-α') : ℂ) * w) = 1 := by linear_combination -h0
      rw [show (1 - (Real.exp (-(2 * α')) : ℂ)) * ((Real.exp (-α') : ℂ) * w) *
          preSchwarzian f ((Real.exp (-α') : ℂ) * w) = -1 by linear_combination -hq1] at hq
      norm_num at hq
  obtain ⟨τ, hτ, hinjC⟩ := loew_injOn_small_time (F := C) (φ := fun t => Φ t α') (F₀ := fh) (G := C α')
    (τ₀ := τ₀) (r₀ := r₀) (ρ := Real.exp (α' / 4)) hτ₀0 hr₀ρ hfc hfi hX4
    (hCd α' hα'0 hα'α) hG'
    (fun t ht => hΦc t α' ht.1 (ht.2.trans hτ₀α'.le) hα'α)
    (fun t ht => hΦi t α' ht.1 (ht.2.trans hτ₀α'.le) hα'α)
    (fun t ht z hz => by
      refine mem_closedBall_zero_iff.mpr ((hΦb t α' ht.1 (ht.2.trans hτ₀α'.le) hα'α z hz).trans ?_)
      calc Real.exp (-(1 / 3 * (α' - t))) * ‖z‖ ≤ r₀ * 1 := by
            refine mul_le_mul (Real.exp_le_exp.mpr (by nlinarith [ht.2])) (mem_closedBall_zero_iff.mp hz)
              (norm_nonneg _) (Real.exp_pos _).le
        _ = r₀ := mul_one _)
    (fun t ht z hz => hΦe t α' ht.1 (ht.2.trans hτ₀α'.le) hα'α z hz)
  have hτ0 : 0 < τ := hτ.1
  have hτα : τ < α := hτ.2.trans_lt (hτ₀α'.trans hα'α)
  -- nesting `C_s(𝔻̄) ⊂ C_t(𝔻)` and `f̂(𝔻̄) ⊂ C_t(𝔻)`
  have hN1 : ∀ s t : ℝ, 0 < s → s < t → t ≤ τ → ∀ z ∈ closedBall (0 : ℂ) 1,
      ∃ u : ℂ, ‖u‖ < 1 ∧ C s z = C t u := by
    intro s t hs hst ht z hz
    refine ⟨Φ s t z, ?_, hΦe s t hs hst.le (ht.trans_lt hτα) z hz⟩
    refine lt_of_le_of_lt (hΦb s t hs hst.le (ht.trans_lt hτα) z hz) ?_
    calc Real.exp (-(1 / 3 * (t - s))) * ‖z‖ ≤ Real.exp (-(1 / 3 * (t - s))) * 1 :=
          mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hz) (Real.exp_pos _).le
      _ < 1 := by rw [mul_one]; exact hexp1 _ (by nlinarith)
  have hN0 : ∀ t : ℝ, 0 < t → t ≤ τ → ∀ z ∈ closedBall (0 : ℂ) 1,
      ∃ u : ℂ, ‖u‖ < 1 ∧ fh z = C t u := by
    intro t ht htτ z hz
    have htα : t < α := htτ.trans_lt hτα
    set r₁ : ℝ := Real.exp (-(1 / 3 * (t / 2))) with hr₁
    have hr₁1 : r₁ < 1 := hexp1 _ (by positivity)
    have hsub : closedBall (0 : ℂ) r₁ ⊆ ball (0 : ℂ) (Real.exp (t / 4)) := fun u hu =>
      mem_ball_zero_iff.mpr (((mem_closedBall_zero_iff.mp hu).trans hr₁1.le).trans_lt (hexp1' _ (by linarith)))
    have hKc : IsClosed (C t '' closedBall (0 : ℂ) r₁) :=
      ((isCompact_closedBall _ _).image_of_continuousOn ((hCd t ht htα).continuousOn.mono hsub)).isClosed
    have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), C s z ∈ C t '' closedBall (0 : ℂ) r₁ := by
      filter_upwards [Ioo_mem_nhdsGT (half_pos ht)] with s hs
      refine ⟨Φ s t z, mem_closedBall_zero_iff.mpr ?_, (hΦe s t hs.1 (by linarith [hs.2]) htα z hz).symm⟩
      refine (hΦb s t hs.1 (by linarith [hs.2]) htα z hz).trans ?_
      calc Real.exp (-(1 / 3 * (t - s))) * ‖z‖ ≤ r₁ * 1 :=
            mul_le_mul (Real.exp_le_exp.mpr (by nlinarith [hs.2])) (mem_closedBall_zero_iff.mp hz)
              (norm_nonneg _) (Real.exp_pos _).le
        _ = r₁ := mul_one _
    obtain ⟨u, hu, hEq⟩ := hKc.mem_of_tendsto (hX4.tendsto_at hz) hev
    exact ⟨u, ((mem_closedBall_zero_iff.mp hu).trans_lt hr₁1), hEq.symm⟩
  -- the glued map outside `𝔻̄`
  set Fg : ℂ → ℂ := fun z : ℂ => if ‖z‖ ≤ 1 then fh z else
    f (conj z)⁻¹ + (z - (conj z)⁻¹) * deriv f (conj z)⁻¹ with hFg
  have hrep : ∀ z : ℂ, 1 < ‖z‖ → Fg z = C (Real.log ‖z‖) (z / ‖z‖) := by
    intro z hz
    simp only [hFg, not_le.mpr hz, ↓reduceIte]
    exact ab16x_glue_eq hz
  have hin : ∀ z : ℂ, ‖z‖ ≤ 1 → Fg z = fh z := fun z hz => by simp only [hFg, hz, ↓reduceIte]
  have hζ1 : ∀ z : ℂ, 1 < ‖z‖ → ‖z / ‖z‖‖ = 1 := fun z hz => by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _), div_self (by linarith)]
  have hlog : ∀ z : ℂ, 1 < ‖z‖ → ‖z‖ ≤ Real.exp τ → 0 < Real.log ‖z‖ ∧ Real.log ‖z‖ ≤ τ := by
    intro z hz hzτ
    exact ⟨Real.log_pos hz, (Real.log_le_iff_le_exp (by linarith)).mpr hzτ⟩
  refine ⟨τ, hτ0, ?_, ?_⟩
  · -- continuity
    intro z hz
    have hzτ : ‖z‖ ≤ Real.exp τ := mem_closedBall_zero_iff.mp hz
    rcases lt_trichotomy ‖z‖ 1 with h1 | h1 | h1
    · -- inside
      have hzD : z ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr h1
      have hca : ContinuousAt fh z := (hfc z (ball_subset_closedBall hzD)).continuousAt
        (closedBall_mem_nhds_of_mem hzD)
      refine (hca.congr ?_).continuousWithinAt
      filter_upwards [isOpen_ball.mem_nhds hzD] with u hu
      exact (hin u (mem_ball_zero_iff.mp hu).le).symm
    · -- on the circle
      rw [Metric.continuousWithinAt_iff]
      intro ε hε
      obtain ⟨κ, hκ, hfcz⟩ := Metric.continuousWithinAt_iff.mp (hfc z (hD1 z h1.le)) (ε / 2) (by positivity)
      have hev := Metric.tendstoUniformlyOn_iff.mp hX4 (ε / 2) (by positivity)
      obtain ⟨θ, hθ, hθs⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).mp hev
      have hθ0 : (0 : ℝ) < θ := hθ
      refine ⟨min (κ / 2) (Real.exp θ - 1), lt_min (by positivity) (by linarith [hexp1' θ hθ0]),
        fun z' hz' hd => ?_⟩
      have hd1 : dist z' z < κ / 2 := hd.trans_le (min_le_left _ _)
      have hd2 : dist z' z < Real.exp θ - 1 := hd.trans_le (min_le_right _ _)
      rw [hin z h1.le]
      by_cases hz'1 : ‖z'‖ ≤ 1
      · rw [hin z' hz'1]
        exact (hfcz (hD1 z' hz'1) (by linarith)).trans (by linarith)
      rw [not_le] at hz'1
      have hnorm : ‖z'‖ - 1 ≤ dist z' z := by
        rw [dist_eq_norm, ← h1]
        exact norm_sub_norm_le z' z
      obtain ⟨hl0, -⟩ := hlog z' hz'1 (mem_closedBall_zero_iff.mp hz')
      have hlθ : Real.log ‖z'‖ < θ := by
        rw [Real.log_lt_iff_lt_exp (by linarith)]
        linarith
      rw [hrep z' hz'1]
      have hζD := hD1 _ (hζ1 z' hz'1).le
      have h1' := hθs ⟨hl0, hlθ⟩ (z' / ‖z'‖) hζD
      have hdz : dist (z' / ‖z'‖) z < κ := by
        have he : dist (z' / ‖z'‖) z' = ‖z'‖ - 1 := by
          rw [dist_eq_norm]
          have hn0 : (‖z'‖ : ℂ) ≠ 0 := by exact_mod_cast (show ‖z'‖ ≠ 0 by linarith)
          have : z' / ‖z'‖ - z' = z' * ((1 - ‖z'‖ : ℝ) / ‖z'‖ : ℝ) := by push_cast; field_simp
          rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div,
            abs_of_nonpos (by linarith), abs_of_pos (by linarith)]
          field_simp
          ring
        calc dist (z' / ‖z'‖) z ≤ dist (z' / ‖z'‖) z' + dist z' z := dist_triangle _ _ _
          _ < κ := by rw [he]; linarith
      have h2 := hfcz hζD hdz
      calc dist (C (Real.log ‖z'‖) (z' / ‖z'‖)) (fh z)
          ≤ dist (C (Real.log ‖z'‖) (z' / ‖z'‖)) (fh (z' / ‖z'‖)) + dist (fh (z' / ‖z'‖)) (fh z) :=
            dist_triangle _ _ _
        _ < ε / 2 + ε / 2 := by rw [dist_comm] at h1'; exact add_lt_add h1' h2
        _ = ε := by ring
    · -- outside
      have hzE : (conj z)⁻¹ ∈ unitDisc := by
        refine mem_ball_zero_iff.mpr ?_
        rw [norm_inv, Complex.norm_conj]
        exact inv_lt_one_of_one_lt₀ h1
      have hz0 : conj z ≠ 0 := (map_ne_zero _).mpr (norm_pos_iff.mp (by linarith))
      have hci : ContinuousAt (fun u : ℂ => (conj u)⁻¹) z :=
        (Complex.continuous_conj.continuousAt).inv₀ hz0
      have hfa : ContinuousAt f (conj z)⁻¹ := hf.continuousOn.continuousAt (isOpen_ball.mem_nhds hzE)
      have hdfa : ContinuousAt (deriv f) (conj z)⁻¹ :=
        (hf.deriv isOpen_ball).continuousOn.continuousAt (isOpen_ball.mem_nhds hzE)
      have hc1 : ContinuousAt (fun u : ℂ => f (conj u)⁻¹) z :=
        ContinuousAt.comp (g := f) (f := fun u : ℂ => (conj u)⁻¹) hfa hci
      have hc2 : ContinuousAt (fun u : ℂ => deriv f (conj u)⁻¹) z :=
        ContinuousAt.comp (g := deriv f) (f := fun u : ℂ => (conj u)⁻¹) hdfa hci
      have hform : ContinuousAt (fun u : ℂ => f (conj u)⁻¹ + (u - (conj u)⁻¹) * deriv f (conj u)⁻¹) z :=
        hc1.add ((continuousAt_id.sub hci).mul hc2)
      refine (hform.congr ?_).continuousWithinAt
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds h1] with u hu
      simp only [hFg, not_le.mpr hu, ↓reduceIte]
  · -- injectivity
    intro z₁ h₁ z₂ h₂ he
    have h₁τ := mem_closedBall_zero_iff.mp h₁
    have h₂τ := mem_closedBall_zero_iff.mp h₂
    -- a point inside cannot meet a point outside
    have hmix : ∀ a b : ℂ, ‖a‖ ≤ 1 → 1 < ‖b‖ → ‖b‖ ≤ Real.exp τ → Fg a ≠ Fg b := by
      intro a b ha hb hbτ hab
      obtain ⟨hl0, hlτ⟩ := hlog b hb hbτ
      obtain ⟨u, hu, hEq⟩ := hN0 _ hl0 hlτ a (hD1 a ha)
      rw [hin a ha, hrep b hb, hEq] at hab
      have := hinjC _ ⟨hl0, hlτ⟩ (hD1 u hu.le) (hD1 _ (hζ1 b hb).le) hab
      rw [this, hζ1 b hb] at hu
      exact lt_irrefl _ hu
    -- two points outside at different radii cannot meet
    have hrad : ∀ a b : ℂ, 1 < ‖a‖ → 1 < ‖b‖ → ‖b‖ ≤ Real.exp τ →
        Real.log ‖a‖ < Real.log ‖b‖ → Fg a ≠ Fg b := by
      intro a b ha hb hbτ hlt hab
      obtain ⟨hla, -⟩ := hlog a ha (by
        have := (Real.log_lt_log_iff (by linarith) (by linarith)).mp hlt
        linarith)
      obtain ⟨hlb, hlbτ⟩ := hlog b hb hbτ
      obtain ⟨u, hu, hEq⟩ := hN1 _ _ hla hlt hlbτ (a / ‖a‖) (hD1 _ (hζ1 a ha).le)
      rw [hrep a ha, hrep b hb, hEq] at hab
      have := hinjC _ ⟨hlb, hlbτ⟩ (hD1 u hu.le) (hD1 _ (hζ1 b hb).le) hab
      rw [this, hζ1 b hb] at hu
      exact lt_irrefl _ hu
    rcases le_or_gt ‖z₁‖ 1 with c₁ | c₁ <;> rcases le_or_gt ‖z₂‖ 1 with c₂ | c₂
    · rw [hin z₁ c₁, hin z₂ c₂] at he
      exact hfi (hD1 z₁ c₁) (hD1 z₂ c₂) he
    · exact absurd he (hmix z₁ z₂ c₁ c₂ h₂τ)
    · exact absurd he.symm (hmix z₂ z₁ c₂ c₁ h₁τ)
    · rcases lt_trichotomy (Real.log ‖z₁‖) (Real.log ‖z₂‖) with hl | hl | hl
      · exact absurd he (hrad z₁ z₂ c₁ c₂ h₂τ hl)
      · obtain ⟨hl0, hlτ⟩ := hlog z₁ c₁ h₁τ
        have heq := he
        rw [hrep z₁ c₁, hrep z₂ c₂, ← hl] at heq
        have hζ := hinjC _ ⟨hl0, hlτ⟩ (hD1 _ (hζ1 z₁ c₁).le) (hD1 _ (hζ1 z₂ c₂).le) heq
        have hn : ‖z₁‖ = ‖z₂‖ := Real.log_injOn_pos (Set.mem_Ioi.mpr (by linarith))
          (Set.mem_Ioi.mpr (by linarith)) hl
        have hn0 : (‖z₁‖ : ℂ) ≠ 0 := by exact_mod_cast (show ‖z₁‖ ≠ 0 by linarith)
        rw [hn] at hζ hn0
        exact (div_left_inj' hn0).mp hζ
      · exact absurd he.symm (hrad z₂ z₁ c₂ c₁ h₁τ hl)

/-- A vertical line meets the unit circle in at most two points. -/
theorem ab16x_circle_slice (x : ℝ) : {y : ℝ | (x : ℂ) + (y : ℂ) * I ∈ sphere (0 : ℂ) 1}.Countable ∧
    {y : ℝ | (y : ℂ) + (x : ℂ) * I ∈ sphere (0 : ℂ) 1}.Countable := by
  have key : ∀ a b : ℝ, (a : ℂ) + (b : ℂ) * I ∈ sphere (0 : ℂ) 1 →
      b = Real.sqrt (1 - a ^ 2) ∨ b = -Real.sqrt (1 - a ^ 2) := by
    intro a b h
    have h1 : ‖(a : ℂ) + (b : ℂ) * I‖ ^ 2 = 1 := by rw [mem_sphere_zero_iff_norm.mp h]; norm_num
    rw [Complex.sq_norm, Complex.normSq_add_mul_I] at h1
    have hnn : 0 ≤ 1 - a ^ 2 := by nlinarith [sq_nonneg b]
    rw [← sq_eq_sq_iff_eq_or_eq_neg, Real.sq_sqrt hnn]
    linarith
  constructor
  · refine ((Set.toFinite ({Real.sqrt (1 - x ^ 2), -Real.sqrt (1 - x ^ 2)} : Set ℝ)).subset ?_).countable
    intro y hy
    rcases key x y hy with h | h <;> simp [h]
  · refine ((Set.toFinite ({Real.sqrt (1 - x ^ 2), -Real.sqrt (1 - x ^ 2)} : Set ℝ)).subset ?_).countable
    intro y hy
    have hy' : (x : ℂ) + (y : ℂ) * I ∈ sphere (0 : ℂ) 1 := by
      have h1 : ‖(y : ℂ) + (x : ℂ) * I‖ = 1 := mem_sphere_zero_iff_norm.mp hy
      refine mem_sphere_zero_iff_norm.mpr ?_
      have h2 : ‖(y : ℂ) + (x : ℂ) * I‖ ^ 2 = ‖(x : ℂ) + (y : ℂ) * I‖ ^ 2 := by
        rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_add_mul_I, Complex.normSq_add_mul_I]; ring
      rw [h1] at h2
      nlinarith [norm_nonneg ((x : ℂ) + (y : ℂ) * I)]
    rcases key x y hy' with h | h <;> simp [h]

/-- `|1/z̄| = 1/|z|` and `|z - 1/z̄| = |z| - 1/|z|` for `|z| > 1`. -/
theorem ab16x_conj_inv_norms {z : ℂ} (hz : 1 < ‖z‖) :
    ‖(conj z)⁻¹‖ = ‖z‖⁻¹ ∧ ‖z - (conj z)⁻¹‖ = ‖z‖ - ‖z‖⁻¹ := by
  have hn : 0 < ‖z‖ := by linarith
  have hz0 : z ≠ 0 := norm_pos_iff.mp hn
  refine ⟨by rw [norm_inv, Complex.norm_conj], ?_⟩
  have hinv : (conj z)⁻¹ = z / (‖z‖ : ℂ) ^ 2 := by
    rw [← Complex.mul_conj']
    have : conj z ≠ 0 := (map_ne_zero _).mpr hz0
    field_simp
  have he : z - (conj z)⁻¹ = ((1 - ‖z‖⁻¹ ^ 2 : ℝ) : ℂ) * z := by
    rw [hinv]
    have hn0 : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    push_cast
    field_simp
  have hpos : 0 ≤ 1 - ‖z‖⁻¹ ^ 2 := by
    have : ‖z‖⁻¹ < 1 := inv_lt_one_of_one_lt₀ hz
    nlinarith [inv_pos.mpr hn]
  rw [he, norm_mul, Complex.norm_real, Real.norm_of_nonneg hpos]
  field_simp

/-- The glued map is quasiconformal on a disc `|z| < R`, `R > 1` (removability of `S¹`, `s13x_removable`). -/
theorem ab16x_qc {f fh : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc)
    (hA : Tendsto (fun z => ((1 - ‖z‖ ^ 2) : ℂ) * preSchwarzian f z)
      (comap (fun z : ℂ => ‖z‖) (𝓝[<] 1)) (𝓝 0))
    (hfc : ContinuousOn fh (closedBall (0 : ℂ) 1)) (hfi : InjOn fh (closedBall (0 : ℂ) 1))
    (hfe : EqOn fh f unitDisc) :
    ∃ R > 1, IsQuasiconformal (fun z : ℂ => if ‖z‖ ≤ 1 then fh z else
        f (conj z)⁻¹ + (z - (conj z)⁻¹) * deriv f (conj z)⁻¹) (ball 0 R) := by
  obtain ⟨τ, hτ, hcont, hinjg⟩ := ab16x_glue_injective hf hinj hA hfc hfi hfe
  obtain ⟨r, hr1, hr⟩ := (ab16_tendsto_iff.mp hA) (1 / 2) (by norm_num)
  set Fg : ℂ → ℂ := fun z : ℂ => if ‖z‖ ≤ 1 then fh z else
    f (conj z)⁻¹ + (z - (conj z)⁻¹) * deriv f (conj z)⁻¹ with hFg
  set G : ℂ → ℂ := fun u : ℂ => f (conj u)⁻¹ + (u - (conj u)⁻¹) * deriv f (conj u)⁻¹ with hG
  set r' : ℝ := max r (1 / 2) with hr'
  have hr'0 : 0 < r' := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hr'1 : r' < 1 := max_lt hr1 (by norm_num)
  set R : ℝ := min (Real.exp τ) r'⁻¹ with hRd
  have hexpτ : 1 < Real.exp τ := by
    calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
      _ < Real.exp τ := Real.exp_lt_exp.mpr hτ
  have hR1 : 1 < R := lt_min hexpτ ((one_lt_inv₀ hr'0).mpr hr'1)
  have hΩsub : ball (0 : ℂ) R ⊆ closedBall (0 : ℂ) (Real.exp τ) := fun z hz =>
    mem_closedBall_zero_iff.mpr ((mem_ball_zero_iff.mp hz).le.trans (min_le_left _ _))
  have hhom : IsHomeomorphOnto Fg (ball (0 : ℂ) R) (Fg '' ball (0 : ℂ) R) :=
    qcl_f_isHomeomorphOnto_of_injOn isOpen_ball (hcont.mono hΩsub) (hinjg.mono hΩsub)
  refine ⟨R, hR1, 3, s13x_removable (L := sphere (0 : ℂ) 1) isOpen_ball (by norm_num) hhom
    (Measure.addHaar_sphere (μ := volume) (0 : ℂ) 1)
    (Eventually.of_forall fun x => (ab16x_circle_slice x).1)
    (Eventually.of_forall fun y => (ab16x_circle_slice y).2) ?_⟩
  rintro z ⟨hzΩ, hzL⟩
  have hz1 : ‖z‖ ≠ 1 := fun h => hzL (mem_sphere_zero_iff_norm.mpr h)
  rcases lt_or_gt_of_ne hz1 with h1 | h1
  · -- inside: conformal
    refine ⟨ball (0 : ℂ) 1, isOpen_ball, mem_ball_zero_iff.mpr h1,
      ball_subset_ball hR1.le, ?_⟩
    have hK1 : IsKQC f unitDisc 1 := isKQC_one_of_conformal isOpen_ball ⟨hf, hinj, rfl⟩
    refine ad_isKQC_congr (hK1.mono (by norm_num)) (fun u hu => ?_)
    have hu1 : ‖u‖ ≤ 1 := (mem_ball_zero_iff.mp hu).le
    simp only [hFg, hu1, ↓reduceIte]
    exact hfe hu
  · -- outside: `C¹` with `|μ| < 1/2`
    set U : Set ℂ := {w : ℂ | 1 < ‖w‖} ∩ ball (0 : ℂ) R with hU
    have hUo : IsOpen U := (isOpen_lt continuous_const continuous_norm).inter isOpen_ball
    have hUsub : U ⊆ ball (0 : ℂ) R := inter_subset_right
    have hFG : EqOn Fg G U := fun w hw => by
      have : ¬ ‖w‖ ≤ 1 := not_le.mpr hw.1
      simp only [hFg, hG, this, ↓reduceIte]
    refine ⟨U, hUo, ⟨h1, hzΩ⟩, hUsub, ad_isKQC_congr (isKQC_of_isC1Quasiconformal ?_) hFG⟩
    refine ⟨hUo, by norm_num, fun w hw => (ab16x_ext_dilatation hf hinj hw.1).1.contDiffWithinAt,
      qcl_f_isHomeomorphOnto_of_injOn hUo
        (fun w hw => (ab16x_ext_dilatation hf hinj hw.1).1.continuousAt.continuousWithinAt)
        ((hinjg.mono (hUsub.trans hΩsub)).congr hFG), fun w hw => ?_⟩
    obtain ⟨-, hdz, hmu⟩ := ab16x_ext_dilatation hf hinj hw.1
    have hw1 : 1 < ‖w‖ := hw.1
    have hwR : ‖w‖ < R := mem_ball_zero_iff.mp hw.2
    obtain ⟨hun, hdn⟩ := ab16x_conj_inv_norms hw1
    have hn : 0 < ‖w‖ := by linarith
    have huD : (conj w)⁻¹ ∈ unitDisc := by
      refine mem_ball_zero_iff.mpr ?_
      rw [hun]
      exact inv_lt_one_of_one_lt₀ hw1
    have hdz0 : dz G w ≠ 0 := by
      rw [hdz]
      exact deriv_ne_zero_of_injOn isOpen_ball hf hinj huD
    -- `|μ| ≤ (1 - |u|²)|𝒜f(u)| < 1/2`
    have hur : r < ‖(conj w)⁻¹‖ := by
      rw [hun]
      have : ‖w‖ < r'⁻¹ := hwR.trans_le (min_le_right _ _)
      have h2 : r' < ‖w‖⁻¹ := by
        rw [lt_inv_comm₀ hr'0 hn]
        exact this
      exact lt_of_le_of_lt (le_max_left _ _) h2
    have hA2 := hr (conj w)⁻¹ hur (mem_ball_zero_iff.mp huD)
    have hcast : ‖((1 - ‖(conj w)⁻¹‖ ^ 2 : ℝ) : ℂ) * preSchwarzian f (conj w)⁻¹‖ =
        (1 - ‖w‖⁻¹ ^ 2) * ‖preSchwarzian f (conj w)⁻¹‖ := by
      rw [norm_mul, Complex.norm_real, hun, Real.norm_of_nonneg]
      have : ‖w‖⁻¹ < 1 := inv_lt_one_of_one_lt₀ hw1
      nlinarith [inv_pos.mpr hn]
    have hA2' : (1 - ‖w‖⁻¹ ^ 2) * ‖preSchwarzian f (conj w)⁻¹‖ < 1 / 2 := by
      rw [← hcast]
      simpa using hA2
    have hmu_le : ‖complexDilatation G w‖ < 1 / 2 := by
      rw [hmu, norm_div, norm_mul, norm_neg, hdn, norm_pow, Complex.norm_conj]
      have hP := norm_nonneg (preSchwarzian f (conj w)⁻¹)
      have he : (‖w‖ - ‖w‖⁻¹) * ‖preSchwarzian f (conj w)⁻¹‖ / ‖w‖ ^ 2 =
          (1 - ‖w‖⁻¹ ^ 2) * ‖preSchwarzian f (conj w)⁻¹‖ * ‖w‖⁻¹ := by
        field_simp
      rw [he]
      have hwi : ‖w‖⁻¹ < 1 := inv_lt_one_of_one_lt₀ hw1
      have hnn : 0 ≤ (1 - ‖w‖⁻¹ ^ 2) * ‖preSchwarzian f (conj w)⁻¹‖ :=
        mul_nonneg (by nlinarith [inv_pos.mpr hn]) hP
      nlinarith [inv_pos.mpr hn]
    have hdzbar : dzbar G w = complexDilatation G w * dz G w := by
      simp only [complexDilatation]
      field_simp
    constructor
    · rw [hdzbar, norm_mul]
      have := norm_pos_iff.mpr hdz0
      nlinarith [norm_nonneg (complexDilatation G w)]
    · simp only [dilatationQuotient]
      rw [div_le_iff₀ (by linarith)]
      linarith


/-- **(iii) ⇒ (i)** of Theorem 1.6 (Becker–Pommerenke, BP78 Satz 4). Frozen statement (agreed with 下属4). -/
theorem ab16_iii_imp_i {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc)
    (hJ : IsJordanDomain (f '' unitDisc)) (hb : Bornology.IsBounded (f '' unitDisc))
    (hA : Tendsto (fun z => ((1 - ‖z‖ ^ 2) : ℂ) * preSchwarzian f z)
      (comap (fun z : ℂ => ‖z‖) (𝓝[<] 1)) (𝓝 0)) :
    ∃ R > 1, ∃ F : ℂ → ℂ, IsQuasiconformal F (ball 0 R) ∧ EqOn F f unitDisc ∧
      Tendsto (complexDilatation F) (comap (fun z : ℂ => ‖z‖) (𝓝[>] 1)) (𝓝 0) := by
  obtain ⟨fh, hfc, hfi, hfe⟩ := ab16x_caratheodory hf hinj hJ hb
  obtain ⟨R, hR, hq⟩ := ab16x_qc hf hinj hA hfc hfi hfe
  refine ⟨R, hR, _, hq, fun z hz => ?_, ab16x_dilatation_tendsto hf hinj hA⟩
  have hz1 : ‖z‖ ≤ 1 := (mem_ball_zero_iff.mp hz).le
  simp only [hz1, ↓reduceIte]
  exact hfe hz

end Ch2

end TakhtajanTeo
