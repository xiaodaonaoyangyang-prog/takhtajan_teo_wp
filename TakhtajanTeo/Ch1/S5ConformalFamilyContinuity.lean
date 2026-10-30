import TakhtajanTeo.Ch1.S5ConformalFamily
import TakhtajanTeo.Ch1.WRegFoundation

/-! Joint continuity and genuine conformal transition domains for the complexified family. -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

section LinearFamily
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (T : E → ℂ → ℂ) (hT : ∀ v, IsBeltramiCoeff (T v) univ ‖v‖)
variable (hlin : ∀ (a : ℂ) v w, T (a • v + w) =ᵐ[volume] fun z => a * T v z + T w z)
include hT hlin

-- L1
theorem s5cf_linear_family_luc {v₀ : E} (hv₀ : v₀ ∈ ball 0 1)
    {vs : ℕ → E} (hlim : Tendsto vs atTop (𝓝 v₀)) :
    TendstoLocallyUniformly (fun n => normalizedSolution (T (vs n)))
      (normalizedSolution (T v₀)) atTop := by
  have hv : ‖v₀‖ < 1 := mem_ball_zero_iff.mp hv₀
  let k := (‖v₀‖ + 1) / 2
  have hk0 : 0 ≤ k := by dsimp [k]; positivity
  have hk1 : k < 1 := by dsimp [k]; linarith
  have hvk : ‖v₀‖ < k := by dsimp [k]; linarith
  have hpt : ∀ z, Tendsto (fun n => normalizedSolution (T (vs n)) z) atTop
      (𝓝 (normalizedSolution (T v₀) z)) := fun z =>
    ((s5cf_linear_family_differentiableOn T hT hlin z).differentiableAt
      (isOpen_ball.mem_nhds hv₀)).continuousAt.tendsto.comp hlim
  have hqc : ∀ᶠ n in atTop, IsKQCNormalizedPlane (normalizedSolution (T (vs n)))
      ((1 + k) / (1 - k)) := by
    filter_upwards [(continuous_norm.tendsto v₀ |>.comp hlim).eventually (gt_mem_nhds hvk)] with n hn
    have hcoeff : IsBeltramiCoeff (T (vs n)) univ k :=
      ⟨(hT (vs n)).1, (hT (vs n)).2.mono fun _ hu => hu.trans hn.le⟩
    exact wr_ns_qc hk0 hk1 hcoeff le_rfl
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro S hS
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  by_contra hcon
  rw [not_eventually] at hcon
  obtain ⟨N, hN⟩ := eventually_atTop.1 hqc
  obtain ⟨φ, hφ, hbad⟩ := extraction_of_frequently_atTop (hcon.and_eventually (eventually_ge_atTop N))
  have hK' : ∀ n, IsKQCNormalizedPlane (normalizedSolution (T (vs (φ n))))
      ((1 + k) / (1 - k)) := fun n => hN _ (hbad n).2
  obtain ⟨ψ, hψ, G, hG⟩ := UniversalTeichmuller.ut2_nf_extract hK'
  have hGeq : G = normalizedSolution (T v₀) := by
    funext w
    exact tendsto_nhds_unique
      ((tendstoLocallyUniformly_iff_forall_isCompact.1 hG {w} isCompact_singleton).tendsto_at (mem_singleton w))
      ((hpt w).comp (hφ.tendsto_atTop.comp hψ.tendsto_atTop))
  rw [hGeq] at hG
  have hU := Metric.tendstoUniformlyOn_iff.1 (tendstoLocallyUniformly_iff_forall_isCompact.1 hG S hS) ε hε
  obtain ⟨n, hn⟩ := hU.exists
  exact (hbad (ψ n)).1 hn

-- L2
theorem s5cf_linear_family_cont :
    ContinuousOn (fun q : E × ℂ => normalizedSolution (T q.1) q.2) (ball 0 1 ×ˢ univ) := by
  rintro ⟨v₀, z₀⟩ ⟨hv₀, -⟩
  show Tendsto _ (𝓝[ball 0 1 ×ˢ univ] (v₀, z₀)) _
  rw [Filter.tendsto_iff_seq_tendsto]
  intro x hx
  have hx' := tendsto_nhdsWithin_iff.mp hx
  have h1 : Tendsto (fun n => (x n).1) atTop (𝓝 v₀) := (continuous_fst.tendsto _).comp hx'.1
  have h2 : Tendsto (fun n => (x n).2) atTop (𝓝 z₀) := (continuous_snd.tendsto _).comp hx'.1
  have hL := s5cf_linear_family_luc T hT hlin hv₀ h1
  have hqc := wr_ns_qc (norm_nonneg v₀) (mem_ball_zero_iff.mp hv₀) (hT v₀) le_rfl
  have hc : Continuous (normalizedSolution (T v₀)) := continuousOn_univ.1 hqc.1.2.2.1.1
  exact hL.tendsto_comp hc.continuousAt h2

-- L3
theorem s5cf_linear_family_inv_cont :
    ContinuousOn (fun q : E × ℂ => Function.invFun (normalizedSolution (T q.1)) q.2)
      (ball 0 1 ×ˢ univ) := by
  rintro ⟨v₀, z₀⟩ ⟨hv₀, -⟩
  show Tendsto _ (𝓝[ball 0 1 ×ˢ univ] (v₀, z₀)) _
  rw [Filter.tendsto_iff_seq_tendsto]
  intro x hx
  have hx' := tendsto_nhdsWithin_iff.mp hx
  have h1 : Tendsto (fun n => (x n).1) atTop (𝓝 v₀) := (continuous_fst.tendsto _).comp hx'.1
  have h2 : Tendsto (fun n => (x n).2) atTop (𝓝 z₀) := (continuous_snd.tendsto _).comp hx'.1
  have hL := s5cf_linear_family_luc T hT hlin hv₀ h1
  obtain ⟨N, hN⟩ := eventually_atTop.1 hx'.2
  have he : ∀ n, ∃ e : ℂ ≃ₜ ℂ, ⇑e = normalizedSolution (T (x (n + N)).1) := by
    intro n
    have hv := (hN (n + N) (by omega)).1
    have h := wr_ns_qc (norm_nonneg (x (n + N)).1) (mem_ball_zero_iff.mp hv) (hT _) le_rfl
    exact t1_homeomorph h.1 h.2.1
  choose e he using he
  have hW0 := wr_ns_qc (norm_nonneg v₀) (mem_ball_zero_iff.mp hv₀) (hT v₀) le_rfl
  obtain ⟨e₀, he₀⟩ := t1_homeomorph hW0.1 hW0.2.1
  have hLE : TendstoLocallyUniformly (fun n => ⇑(e n)) ⇑e₀ atTop := by
    rw [tendstoLocallyUniformly_iff_forall_isCompact] at hL ⊢
    intro K hK
    have h := hL K hK
    rw [Metric.tendstoUniformlyOn_iff] at h ⊢
    intro ε hε
    filter_upwards [(tendsto_add_atTop_nat N).eventually (h ε hε)] with n hn
    intro z hz
    rw [he₀, he n]
    exact hn z hz
  have hinv := kn6_inverse_locallyUniform hLE
  have h2' : Tendsto (fun n => (x (n + N)).2) atTop (𝓝 z₀) := (tendsto_add_atTop_iff_nat N).2 h2
  have hlim := hinv.tendsto_comp e₀.symm.continuous.continuousAt h2'
  have hval : Function.invFun (normalizedSolution (T v₀)) z₀ = e₀.symm z₀ := wr_invFun_eq he₀ z₀
  show Tendsto (fun n => Function.invFun (normalizedSolution (T (x n).1)) (x n).2) atTop
    (𝓝 (Function.invFun (normalizedSolution (T v₀)) z₀))
  rw [hval, ← tendsto_add_atTop_iff_nat N]
  refine hlim.congr fun n => ?_
  show (e n).symm (x (n + N)).2 = _
  rw [wr_invFun_eq (he n)]

end LinearFamily

-- L4
theorem s5cf_coeff_exterior (p : LinfStar × LinfStar) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    s5cf_coeff p z = extB p.1 z := by
  have hD : z ∉ unitDisc := fun h => (not_lt_of_ge hz.le) (mem_ball_zero_iff.mp h)
  exact if_neg hD

/-- The actual plane transition, before the welding Möbius normalization. -/
def s5cf_transition (p : LinfStar × LinfStar) : ℂ → ℂ :=
  normalizedSolution (extB p.1) ∘ Function.invFun (normalizedSolution (s5cf_coeff p))

theorem s5cf_coeff_inv_cont :
    ContinuousOn (fun q : (LinfStar × LinfStar) × ℂ =>
      Function.invFun (normalizedSolution (s5cf_coeff q.1)) q.2) (ball 0 1 ×ˢ univ) :=
  s5cf_linear_family_inv_cont s5cf_coeff s5cf_coeff_bound s5cf_coeff_linear

theorem s5cf_planeB_cont :
    ContinuousOn (fun q : LinfStar × ℂ => normalizedSolution (extB q.1) q.2)
      (ball 0 1 ×ˢ univ) :=
  s5cf_linear_family_cont extB extB_isBeltramiCoeff QCV.qcv_extB_lin

-- L5
theorem s5cf_transition_cont :
    ContinuousOn (fun q : (LinfStar × LinfStar) × ℂ => s5cf_transition q.1 q.2)
      (ball 0 1 ×ˢ univ) := by
  change ContinuousOn ((fun q : LinfStar × ℂ => normalizedSolution (extB q.1) q.2) ∘
    (fun q : (LinfStar × LinfStar) × ℂ =>
      (q.1.1, Function.invFun (normalizedSolution (s5cf_coeff q.1)) q.2))) (ball 0 1 ×ˢ univ)
  have hf : Continuous (fun q : (LinfStar × LinfStar) × ℂ => q.1.1) :=
    continuous_fst.comp continuous_fst
  have hm : ContinuousOn (fun q : (LinfStar × LinfStar) × ℂ =>
      (q.1.1, Function.invFun (normalizedSolution (s5cf_coeff q.1)) q.2))
      (ball 0 1 ×ˢ univ) := hf.continuousOn.prodMk s5cf_coeff_inv_cont
  have hmaps : MapsTo (fun q : (LinfStar × LinfStar) × ℂ =>
      (q.1.1, Function.invFun (normalizedSolution (s5cf_coeff q.1)) q.2))
      (ball 0 1 ×ˢ univ) (ball 0 1 ×ˢ univ) := by
    intro q hq
    exact ⟨mem_ball_zero_iff.mpr ((norm_fst_le q.1).trans_lt (mem_ball_zero_iff.mp hq.1)), mem_univ _⟩
  exact s5cf_planeB_cont.comp hm hmaps

-- L6
theorem s5cf_transition_conformal {p : LinfStar × LinfStar} (hp : p ∈ ball 0 1) :
    IsConformalOnto (s5cf_transition p) (normalizedSolution (s5cf_coeff p) '' unitDiscExterior)
      (normalizedSolution (extB p.1) '' unitDiscExterior) := by
  have hpa : ‖p‖ < 1 := mem_ball_zero_iff.mp hp
  have hpb : ‖p.1‖ < 1 := (norm_fst_le p).trans_lt hpa
  have hA := QCV.qcv_ns_spec (norm_nonneg p) hpa (s5cf_coeff_bound p)
  have hB := QCV.qcv_ns_spec (norm_nonneg p.1) hpb (extB_isBeltramiCoeff p.1)
  obtain ⟨KA, hKA⟩ := hA.1
  obtain ⟨KB, hKB⟩ := hB.1
  have hDo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hKAD := ac_t_isKQC_restrict hKA hDo (subset_univ _)
  have hKBD := ac_t_isKQC_restrict hKB hDo (subset_univ _)
  have hdil : ∀ᵐ z ∂(volume.restrict unitDiscExterior),
      complexDilatation (normalizedSolution (extB p.1)) z =
      complexDilatation (normalizedSolution (s5cf_coeff p)) z := by
    filter_upwards [ae_restrict_of_ae hB.2.2.2.2, ae_restrict_of_ae hA.2.2.2.2,
      ae_restrict_mem hDo.measurableSet] with z h1 h2 hz
    rw [h1, h2, s5cf_coeff_exterior p hz]
  have hc := bg_conformal_of_dilatation_eq hKAD hKBD hdil
  have hi : Function.Injective (normalizedSolution (s5cf_coeff p)) :=
    (injOn_univ).mp hKA.2.2.1.2.1
  have he : EqOn (s5cf_transition p)
      (normalizedSolution (extB p.1) ∘ Function.invFunOn (normalizedSolution (s5cf_coeff p)) unitDiscExterior)
      (normalizedSolution (s5cf_coeff p) '' unitDiscExterior) := by
    rintro _ ⟨z, hz, rfl⟩
    simp only [s5cf_transition, Function.comp_apply, Function.leftInverse_invFun hi z,
      hi.injOn.leftInvOn_invFunOn hz]
  exact ⟨hc.1.congr he, hc.2.1.congr he.symm, he.image_eq.trans hc.2.2⟩

end TakhtajanTeo

