import TakhtajanTeo.Appendix.AppACont
import TakhtajanTeo.Ch1.S5WeldingNormalization
import TakhtajanTeo.Ch2.S1_T112Completed
import References.GardinerLakic2000.Ch01.S05_BeltramiEquation

/-!
# Continuity of Model A under a.e. convergence of Beltrami coefficients (prefix `s36a_`)

Support for `lemma_3_6` (Ch2/S3Lemma36): the dilation approximants `κₙ` converge to `κ` only almost everywhere, not
in `L∞`, so the norm-continuity results of `Appendix/AppACont` do not apply. Here the plane step uses
`GardinerLakic2000.lemma1_1` (normalized solutions converge locally uniformly under a.e. convergence with a uniform
bound `k < 1`); the Möbius renormalization of Model A (`s5cf_wAS_rep`), the passage to `ℂ̄`, the inverses and the
upgrade from continuous convergence to locally uniform convergence follow the shape of `Appendix/AppACont`.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC
namespace Ch2

/-- Reflection `w ↦ 1/w̄` preserves null sets on `𝔻`. -/
theorem s36a_ae_refl {P : ℂ → Prop} (h : ∀ᵐ z, P z) : ∀ᵐ w, w ∈ unitDisc → P (refl w) := by
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.mp h)
  have hK := ab112_refl_lintegral (N.indicator 1)
  have hL : (∫⁻ z in unitDiscExterior, N.indicator 1 z) = 0 := by
    rw [lintegral_indicator_one hNm]
    exact le_antisymm ((Measure.restrict_apply_le _ N).trans hN0.le) bot_le
  rw [hL] at hK
  have hrefl : Measurable refl := by
    unfold refl
    exact measurable_inv.comp Complex.continuous_conj.measurable
  have hmeas : AEMeasurable (fun w => ENNReal.ofReal ((‖w‖ ^ 4)⁻¹) * N.indicator 1 (refl w))
      (volume.restrict unitDisc) :=
    ((ENNReal.measurable_ofReal.comp ((measurable_norm.pow_const 4).inv)).mul
      ((measurable_one.indicator hNm).comp hrefl)).aemeasurable
  have hz := (lintegral_eq_zero_iff' hmeas).mp hK.symm
  have hD : MeasurableSet unitDisc := measurableSet_ball
  filter_upwards [(ae_restrict_iff' hD).mp hz, volume.ae_ne 0] with w hw hw0 hwD
  have h1 := hw hwD
  have hpos : ENNReal.ofReal ((‖w‖ ^ 4)⁻¹) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr (pow_pos (norm_pos_iff.mpr hw0) 4))).ne'
  have h2 : N.indicator 1 (refl w) = (0 : ℝ≥0∞) := by
    simpa [hpos] using h1
  by_contra hP
  have hmem : refl w ∈ N := hNsub hP
  rw [indicator_of_mem hmem] at h2
  exact one_ne_zero h2

/-- a.e. convergence of the Model B extensions gives a.e. convergence of the Model A extensions. -/
theorem s36a_extA_ae {μs : ℕ → LinfStar} {μ₀ : LinfStar}
    (hae : ∀ᵐ z, Tendsto (fun n => extB (μs n) z) atTop (𝓝 (extB μ₀ z))) :
    ∀ᵐ z, Tendsto (fun n => extA (μs n) z) atTop (𝓝 (extA μ₀ z)) := by
  filter_upwards [hae, s36a_ae_refl hae] with z h1 h2
  by_cases hz1 : 1 < ‖z‖
  · have hzE : z ∈ unitDiscExterior := hz1
    simp only [extA, if_pos hz1]
    simpa only [extB, indicator_of_mem hzE] using h1
  · by_cases hz2 : ‖z‖ < 1
    · simp only [extA, if_neg hz1, if_pos hz2]
      by_cases hz0 : z = 0
      · subst hz0
        simp only [zero_pow two_ne_zero, mul_zero, zero_div]
        exact tendsto_const_nhds
      · have hD : z ∈ unitDisc := mem_ball_zero_iff.mpr hz2
        have hrE : refl z ∈ unitDiscExterior := (refl_mem_exterior_iff hz0).mpr hD
        have h3 := h2 hD
        simp only [extB, indicator_of_mem hrE] at h3
        exact (((Complex.continuous_conj.tendsto _).comp h3).mul_const _).div_const _
    · simp only [extA, if_neg hz1, if_neg hz2]
      exact tendsto_const_nhds

/-- The Model A plane solutions converge locally uniformly under a.e. convergence (GL, Lemma 1.1). -/
theorem s36a_WA_luc {μs : ℕ → LinfStar} {μ₀ : LinfStar} {k : ℝ} (hk : k < 1) (hμs : ∀ n, ‖μs n‖ ≤ k)
    (hae : ∀ᵐ z, Tendsto (fun n => extB (μs n) z) atTop (𝓝 (extB μ₀ z))) :
    TendstoLocallyUniformly (fun n => normalizedSolution (extA (μs n))) (normalizedSolution (extA μ₀)) atTop := by
  refine GardinerLakic2000.lemma1_1 hk (fun n => ?_) (s36a_extA_ae hae)
  have h := extA_isBeltramiCoeff (μs n)
  exact ⟨h.1, h.2.mono fun z hz => hz.trans (hμs n)⟩

/-- Quasiconformality bound of the Model A plane solution. -/
theorem s36a_qcA {μ : LinfStar} {k : ℝ} (hk : k < 1) (hμ : ‖μ‖ ≤ k) :
    IsKQCNormalizedPlane (normalizedSolution (extA μ)) ((1 + k) / (1 - k)) := by
  have hk' : ‖μ‖ < 1 := lt_of_le_of_lt hμ hk
  obtain ⟨f, hf, hfK, -⟩ := thm13_7_normalized_existence (norm_nonneg μ) hk' (extA_isBeltramiCoeff μ)
  rw [QCV.qcv_ns_eq (norm_nonneg μ) hk' (extA_isBeltramiCoeff μ) hf]
  have hK : (1 + ‖μ‖) / (1 - ‖μ‖) ≤ (1 + k) / (1 - k) := by
    have h1 : 0 < 1 - k := by linarith
    have h2 : 0 < 1 - ‖μ‖ := by linarith
    rw [div_le_div_iff₀ h2 h1]
    nlinarith [norm_nonneg μ]
  exact ⟨hfK.mono hK, hf.2.1, hf.2.2.1, hf.2.2.2.1⟩

/-- Continuous convergence on `ℂ̄`: locally uniform convergence of normalized `K`-q.c. plane maps gives
`Fₙ(xₙ) → F(x)` whenever `xₙ → x` in `ℂ̄` (at `∞` by `kn6_uniform_proper`). -/
theorem s36a_map_tendsto {F : ℕ → ℂ → ℂ} {F0 : ℂ → ℂ} {K : ℝ} (hF : ∀ n, IsKQCNormalizedPlane (F n) K)
    (hF0 : IsKQCNormalizedPlane F0 K) (hL : TendstoLocallyUniformly F F0 atTop) {x : ℕ → ExtPlane}
    {x0 : ExtPlane} (hx : Tendsto x atTop (𝓝 x0)) :
    Tendsto (fun n => OnePoint.map (F n) (x n)) atTop (𝓝 (OnePoint.map F0 x0)) := by
  have hW0c : Continuous F0 := continuousOn_univ.1 hF0.1.2.2.1.1
  induction x0 using OnePoint.rec with
  | coe z₀ =>
    have hfin : ContinuousAt finPart (z₀ : ExtPlane) :=
      OnePoint.isOpenEmbedding_coe.continuousAt_iff.mp (continuousAt_id : ContinuousAt (fun x : ℂ => x) z₀)
    have hz : Tendsto (fun n => finPart (x n)) atTop (𝓝 z₀) := hfin.tendsto.comp hx
    have hev : ∀ᶠ n in atTop, x n ≠ extInf := by
      filter_upwards [hx.eventually (OnePoint.isOpen_range_coe.mem_nhds ⟨z₀, rfl⟩)] with n hn
      obtain ⟨y, hy⟩ := hn
      rw [← hy]
      exact OnePoint.coe_ne_infty y
    have hval := (OnePoint.continuous_coe.tendsto _).comp (hL.tendsto_comp hW0c.continuousAt hz)
    refine hval.congr' ?_
    filter_upwards [hev] with n hn
    show ((F n (finPart (x n)) : ℂ) : ExtPlane) = OnePoint.map (F n) (x n)
    conv_rhs => rw [← coe_finPart_of_ne hn]
    rfl
  | infty =>
    show Tendsto _ atTop (𝓝 (OnePoint.map F0 extInf))
    rw [show OnePoint.map F0 extInf = extInf from rfl]
    refine OnePoint.hasBasis_nhds_infty.tendsto_right_iff.mpr fun s hs => ?_
    obtain ⟨R₀, hR₀⟩ := hs.2.isBounded.subset_closedBall 0
    set R : ℝ := max R₀ 1
    have hR : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hsR : s ⊆ closedBall 0 R := hR₀.trans (closedBall_subset_closedBall (le_max_left _ _))
    have he : ∀ n, ∃ e : ℂ ≃ₜ ℂ, ⇑e = F n := fun n => t1_homeomorph (hF n).1 (hF n).2.1
    choose E hE using he
    obtain ⟨e₀, he₀⟩ := t1_homeomorph hF0.1 hF0.2.1
    have hLE : TendstoLocallyUniformly (fun n => ⇑(E n)) ⇑e₀ atTop := by
      rw [tendstoLocallyUniformly_iff_forall_isCompact] at hL ⊢
      intro K' hK'
      have h := hL K' hK'
      rw [Metric.tendstoUniformlyOn_iff] at h ⊢
      intro ε hε
      filter_upwards [h ε hε] with n hn
      intro z hz
      rw [he₀, hE n]
      exact hn z hz
    obtain ⟨S, hS0, hSev⟩ := kn6_uniform_proper hLE R hR
    obtain ⟨M, hM⟩ := eventually_atTop.1 hSev
    have hfar : ∀ᶠ n in atTop, x n ∈ (↑) '' (closedBall (0 : ℂ) S)ᶜ ∪ {extInf} :=
      hx.eventually (OnePoint.hasBasis_nhds_infty.mem_of_mem ⟨isClosed_closedBall, isCompact_closedBall 0 S⟩)
    filter_upwards [hfar, eventually_ge_atTop M] with n hn hnM
    rcases hn with ⟨z, hz, hzn⟩ | hinf
    · left
      refine ⟨F n z, fun hzs => ?_, ?_⟩
      · have hzS : S ≤ ‖z‖ := by
          have : ¬ ‖z‖ ≤ S := by simpa [mem_closedBall, dist_zero_right] using hz
          linarith [not_le.mp this]
        have hb := hM n hnM z hzS
        rw [hE n] at hb
        have := hsR hzs
        rw [mem_closedBall, dist_zero_right] at this
        linarith
      · show ((F n z : ℂ) : ExtPlane) = OnePoint.map (F n) (x n)
        rw [← hzn]
        rfl
    · right
      rw [mem_singleton_iff] at hinf ⊢
      show OnePoint.map (F n) (x n) = extInf
      rw [hinf]
      rfl

/-- The Model A normalization coefficients in terms of the plane solution. -/
theorem s36a_coef_eq {μ : LinfStar} (hμ : μ ∈ LinfStarBall) : s5cf_normCoeffs (μ, star μ) =
    s5cf_three_coeff (normalizedSolution (extA μ) (-1)) (normalizedSolution (extA μ) (-I)) := by
  unfold s5cf_normCoeffs
  rw [s5cf_plane_diagonal hμ]

/-- Model A depends continuously on `μ` under a.e. convergence: `w_{μₙ}(xₙ) → w_μ(x)` whenever `xₙ → x` in `ℂ̄`. -/
theorem s36a_wAS_tendsto {μs : ℕ → LinfStar} {μ₀ : LinfStar} {k : ℝ} (hk : k < 1) (hμs : ∀ n, ‖μs n‖ ≤ k)
    (hμ₀ : ‖μ₀‖ ≤ k) (hae : ∀ᵐ z, Tendsto (fun n => extB (μs n) z) atTop (𝓝 (extB μ₀ z)))
    {x : ℕ → ExtPlane} {x0 : ExtPlane} (hx : Tendsto x atTop (𝓝 x0)) :
    Tendsto (fun n => wAS (μs n) (x n)) atTop (𝓝 (wAS μ₀ x0)) := by
  have hball : ∀ μ : LinfStar, ‖μ‖ ≤ k → μ ∈ LinfStarBall := fun μ hμ =>
    mem_ball_zero_iff.mpr (lt_of_le_of_lt hμ hk)
  have hL := s36a_WA_luc hk hμs hae
  have hmap := s36a_map_tendsto (fun n => s36a_qcA hk (hμs n)) (s36a_qcA hk hμ₀) hL hx
  have hcoef : ∀ μ : LinfStar, μ ∈ LinfStarBall → s5cf_normCoeffs (μ, star μ) =
      s5cf_three_coeff (normalizedSolution (extA μ) (-1)) (normalizedSolution (extA μ) (-I)) :=
    fun μ hμ => s36a_coef_eq hμ
  have hcc : Continuous (fun p : ℂ × ℂ => s5cf_three_coeff p.1 p.2) := by
    unfold s5cf_three_coeff
    fun_prop
  have hct : Tendsto (fun n => s5cf_three_coeff (normalizedSolution (extA (μs n)) (-1))
      (normalizedSolution (extA (μs n)) (-I))) atTop
      (𝓝 (s5cf_three_coeff (normalizedSolution (extA μ₀) (-1)) (normalizedSolution (extA μ₀) (-I)))) := by
    have hp : ∀ w : ℂ, Tendsto (fun n => normalizedSolution (extA (μs n)) w) atTop
        (𝓝 (normalizedSolution (extA μ₀) w)) := fun w =>
      (tendstoLocallyUniformly_iff_forall_isCompact.1 hL {w} isCompact_singleton).tendsto_at (mem_singleton w)
    have h0 := (hcc.tendsto _).comp ((hp (-1)).prodMk_nhds (hp (-I)))
    exact h0
  have hdet := s5cf_normCoeffs_det (s5cf_diagonal_mem (hball μ₀ hμ₀))
  rw [hcoef μ₀ (hball μ₀ hμ₀)] at hdet
  have hopen : IsOpen ({x : ℂ × ℂ × ℂ × ℂ | x.1 * x.2.2.2 - x.2.1 * x.2.2.1 ≠ 0} ×ˢ (univ : Set ExtPlane)) :=
    (isOpen_ne_fun (by fun_prop) continuous_const).prod isOpen_univ
  set q0 : (ℂ × ℂ × ℂ × ℂ) × ExtPlane := (s5cf_three_coeff (normalizedSolution (extA μ₀) (-1))
    (normalizedSolution (extA μ₀) (-I)), OnePoint.map (normalizedSolution (extA μ₀)) x0) with hq0
  have hq0m : q0 ∈ {x : ℂ × ℂ × ℂ × ℂ | x.1 * x.2.2.2 - x.2.1 * x.2.2.1 ≠ 0} ×ˢ (univ : Set ExtPlane) :=
    ⟨hdet, mem_univ _⟩
  have hcont := (AppA.acc_mob_cont q0 hq0m).continuousAt (hopen.mem_nhds hq0m)
  have h := hcont.tendsto.comp (hct.prodMk_nhds hmap)
  rw [s5cf_wAS_rep (hball μ₀ hμ₀), hcoef μ₀ (hball μ₀ hμ₀)]
  refine h.congr fun n => ?_
  rw [s5cf_wAS_rep (hball _ (hμs n)) (x n), hcoef _ (hball _ (hμs n))]
  rfl

/-- Inverses: if bijections `Φₙ` of `ℂ̄` converge continuously (along every subsequence) to a bijection `Φ`, then
`Φₙ⁻¹(yₙ) → Φ⁻¹(y)` whenever `yₙ → y`. -/
theorem s36a_inv_tendsto {Φ : ℕ → ExtPlane → ExtPlane} {Φ0 : ExtPlane → ExtPlane}
    (hb : ∀ n, Function.Bijective (Φ n)) (hb0 : Function.Bijective Φ0)
    (hconv : ∀ ψ : ℕ → ℕ, StrictMono ψ → ∀ (x : ℕ → ExtPlane) (x0 : ExtPlane), Tendsto x atTop (𝓝 x0) →
      Tendsto (fun k => Φ (ψ k) (x k)) atTop (𝓝 (Φ0 x0)))
    {y : ℕ → ExtPlane} {y0 : ExtPlane} (hy : Tendsto y atTop (𝓝 y0)) :
    Tendsto (fun n => Function.invFun (Φ n) (y n)) atTop (𝓝 (Function.invFun Φ0 y0)) := by
  haveI := k22_t_firstCountable
  set a := Function.invFun Φ0 y0 with ha
  by_contra hcon
  rw [tendsto_def] at hcon
  push_neg at hcon
  obtain ⟨U, hU, hUev⟩ := hcon
  have hfreq : ∃ᶠ n in atTop, Function.invFun (Φ n) (y n) ∉ U := by
    rw [Filter.Frequently]
    intro h
    exact hUev (by simpa using h)
  obtain ⟨φ, hφ, hbad⟩ := extraction_of_frequently_atTop hfreq
  obtain ⟨b, -, φ', hφ', hlim⟩ := isCompact_univ.tendsto_subseq (x := fun k => Function.invFun (Φ (φ k)) (y (φ k)))
    (fun _ => mem_univ _)
  have h1 := hconv (φ ∘ φ') (hφ.comp hφ') _ b hlim
  have h1' : Tendsto (fun k => y (φ (φ' k))) atTop (𝓝 (Φ0 b)) :=
    h1.congr fun k => Function.rightInverse_invFun (hb _).2 _
  have h3 : Φ0 b = y0 := tendsto_nhds_unique h1' (hy.comp (hφ.comp hφ').tendsto_atTop)
  have hba : b = a := by
    rw [ha, ← h3]
    exact (Function.leftInverse_invFun hb0.1 b).symm
  rw [hba] at hlim
  obtain ⟨k, hk⟩ := (hlim.eventually hU).exists
  exact hbad (φ' k) hk

/-- Continuous convergence (along every subsequence) to a continuous limit is locally uniform convergence. -/
theorem s36a_luc_of_contconv {G : ℕ → ℂ → ℂ} {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hg : ContinuousOn g U)
    (hconv : ∀ ψ : ℕ → ℕ, StrictMono ψ → ∀ (w : ℕ → ℂ) (w0 : ℂ), w0 ∈ U → (∀ k, w k ∈ U) →
      Tendsto w atTop (𝓝 w0) → Tendsto (fun k => G (ψ k) (w k)) atTop (𝓝 (g w0))) :
    TendstoLocallyUniformlyOn G g atTop U := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
  intro S hSU hS
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  by_contra hcon
  rw [not_eventually] at hcon
  have hcon' : ∃ᶠ n in atTop, ∃ w ∈ S, ε ≤ dist (g w) (G n w) := hcon.mono fun n hn => by
    push_neg at hn
    exact hn
  obtain ⟨φ, hφ, hbad⟩ := extraction_of_frequently_atTop hcon'
  choose w hwS hwd using hbad
  obtain ⟨w0, hw0, φ', hφ', hlim⟩ := hS.tendsto_subseq hwS
  have h1 := hconv (φ ∘ φ') (hφ.comp hφ') (w ∘ φ') w0 (hSU hw0) (fun k => hSU (hwS _)) hlim
  have h2 : Tendsto (fun k => g ((w ∘ φ') k)) atTop (𝓝 (g w0)) :=
    ((hg w0 (hSU hw0)).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall
      fun k => hSU (hwS _)⟩))
  have h3 := h2.dist h1
  rw [dist_self] at h3
  obtain ⟨k, hk⟩ := (h3.eventually (gt_mem_nhds hε)).exists
  exact absurd (hwd (φ' k)) (not_le.mpr hk)

end Ch2
end TakhtajanTeo
