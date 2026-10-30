import TakhtajanTeo.Ch1.GroupODELimit
import TakhtajanTeo.Ch1.ComponentMobiusLimit
import TakhtajanTeo.Ch1.ComponentBlowupScaling
import TakhtajanTeo.Ch1.ComponentBlowupSchwarzian
import Mathlib.Analysis.Complex.Convex

open Complex Set Filter Topology Metric
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

def crbl_relative_first (f g : ℂ → ℂ) : ℂ := deriv g 0 / deriv f 0

def crbl_relative_second (f g : ℂ → ℂ) : ℂ :=
  (deriv (deriv g) 0 * deriv f 0 - deriv g 0 * deriv (deriv f) 0) / (deriv f 0)^3

-- L1
/-- A common subsequence of two normalized QC families, with genuine nondegenerate limits. -/
theorem crbl_common_subseq {F G : ℕ → ℂ → ℂ} {K L : ℝ}
    (hF : ∀ n, IsKQCNormalizedPlane (F n) K)
    (hG : ∀ n, IsKQCNormalizedPlane (G n) L) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ f g : ℂ → ℂ,
      IsKQCNormalizedPlane f K ∧ IsKQCNormalizedPlane g L ∧
      TendstoLocallyUniformly (fun n => F (σ n)) f atTop ∧
      TendstoLocallyUniformly (fun n => G (σ n)) g atTop := by
  obtain ⟨σ, hσ, f, hf⟩ := t203_lim_nf_extract hF
  obtain ⟨τ, hτ, g, hg⟩ := t203_lim_nf_extract (fun n => hG (σ n))
  have hf' : TendstoLocallyUniformly (fun n => F (σ (τ n))) f atTop := by
    intro u hu x
    obtain ⟨s, hs, hh⟩ := hf u hu x
    exact ⟨s, hs, hτ.tendsto_atTop.eventually hh⟩
  exact ⟨σ ∘ τ, hσ.comp hτ, f, g,
    t203_lim_nf_limit (fun n => hF (σ (τ n))) hf',
    t203_lim_nf_limit (fun n => hG (σ (τ n))) hg, hf', hg⟩

-- L2
/-- Local eventual holomorphy suffices for Cauchy convergence of three jets. -/
theorem crbl_local_jets {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {U : Set ℂ}
    (hlim : TendstoLocallyUniformlyOn F f atTop U)
    (hlocal : ∀ z ∈ U, ∃ r > 0, ball z r ⊆ U ∧
      ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) (ball z r)) :
    DifferentiableOn ℂ f U ∧ ∀ z ∈ U,
      Tendsto (fun n => deriv (F n) z) atTop (𝓝 (deriv f z)) ∧
      Tendsto (fun n => deriv (deriv (F n)) z) atTop (𝓝 (deriv (deriv f) z)) ∧
      Tendsto (fun n => deriv (deriv (deriv (F n))) z) atTop
        (𝓝 (deriv (deriv (deriv f)) z)) := by
  have hpoint : ∀ z ∈ U, DifferentiableAt ℂ f z ∧
      Tendsto (fun n => deriv (F n) z) atTop (𝓝 (deriv f z)) ∧
      Tendsto (fun n => deriv (deriv (F n)) z) atTop (𝓝 (deriv (deriv f) z)) ∧
      Tendsto (fun n => deriv (deriv (deriv (F n))) z) atTop
        (𝓝 (deriv (deriv (deriv f)) z)) := by
    intro z hz
    obtain ⟨r, hr, hsub, hd⟩ := hlocal z hz
    have hl := hlim.mono hsub
    have h0 : z ∈ ball z r := mem_ball_self hr
    have hd1 := hd.mono (fun n hn => hn.deriv isOpen_ball)
    have hd2 := hd1.mono (fun n hn => hn.deriv isOpen_ball)
    have h1 := hl.deriv hd isOpen_ball
    have h2 := h1.deriv hd1 isOpen_ball
    have h3 := h2.deriv hd2 isOpen_ball
    exact ⟨(hl.differentiableOn hd isOpen_ball).differentiableAt (isOpen_ball.mem_nhds h0),
      h1.tendsto_at h0, h2.tendsto_at h0, h3.tendsto_at h0⟩
  exact ⟨fun z hz => (hpoint z hz).1.differentiableWithinAt, fun z hz => (hpoint z hz).2⟩

-- L3
/-- Schwarzian convergence from three actual jets with nonzero limiting first derivative. -/
theorem crbl_schwarzian_tendsto {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {z : ℂ}
    (hF : ∀ᶠ n in atTop, AnalyticAt ℂ (F n) z) (hf : AnalyticAt ℂ f z)
    (h1 : Tendsto (fun n => deriv (F n) z) atTop (𝓝 (deriv f z)))
    (h2 : Tendsto (fun n => deriv (deriv (F n)) z) atTop (𝓝 (deriv (deriv f) z)))
    (h3 : Tendsto (fun n => deriv (deriv (deriv (F n))) z) atTop
      (𝓝 (deriv (deriv (deriv f)) z))) (hne : deriv f z ≠ 0) :
    Tendsto (fun n => schwarzianHol (F n) z) atTop (𝓝 (schwarzianHol f z)) := by
  have heq : ∀ (g : ℂ → ℂ), AnalyticAt ℂ g z → deriv g z ≠ 0 →
      schwarzianHol g z =
        (deriv (deriv (deriv g)) z * deriv g z - deriv (deriv g) z * deriv (deriv g) z) /
          (deriv g z)^2 - (1/2 : ℂ) * (deriv (deriv g) z / deriv g z)^2 := by
    intro g hg hgn
    unfold schwarzianHol
    congr 1
    exact (hg.deriv.deriv.differentiableAt.hasDerivAt.div
      hg.deriv.differentiableAt.hasDerivAt hgn).deriv
  rw [heq f hf hne]
  have ht := ((h3.mul h1).sub (h2.mul h2)).div (h1.pow 2) (pow_ne_zero 2 hne)
  apply (ht.sub ((h2.div h1 hne).pow 2 |>.const_mul (1/2 : ℂ))).congr'
  filter_upwards [hF, h1.eventually_ne hne] with n hn hnn
  exact (heq (F n) hn hnn).symm

-- L4
/-- Same Schwarzian on an unbounded interior domain forces normalized plane limits to agree there. -/
theorem crbl_rigidity {f g : ℂ → ℂ} {K L : ℝ} {U : Set ℂ}
    (hU : IsOpen U) (hUc : IsConnected U) (hUb : ¬ Bornology.IsBounded U)
    (h0 : (0 : ℂ) ∈ U) (h1 : (1 : ℂ) ∈ U)
    (hf : IsKQCNormalizedPlane f K) (hg : IsKQCNormalizedPlane g L)
    (hfd : DifferentiableOn ℂ f U) (hgd : DifferentiableOn ℂ g U)
    (hS : ∀ z ∈ U, schwarzianHol f z = schwarzianHol g z) : EqOn f g U := by
  obtain ⟨ef, hef⟩ := t203_pack_homeo hf.1 hf.2.1
  obtain ⟨eg, heg⟩ := t203_pack_homeo hg.1 hg.2.1
  subst f
  subst g
  have hfa := hfd.analyticOnNhd hU
  have hga := hgd.analyticOnNhd hU
  obtain ⟨a, b, c, d, hdet, hM⟩ := thm19_1_unique hU hUc
    (isLocUnivMero_of_isConformalOnto hU ⟨hfd, ef.injective.injOn, rfl⟩)
    (isLocUnivMero_of_isConformalOnto hU ⟨hgd, eg.injective.injOn, rfl⟩)
    (fun z hz => by rw [schwarzian_of_analyticAt (hfa z hz),
      schwarzian_of_analyticAt (hga z hz)]; exact hS z hz)
  have himg : ¬ Bornology.IsBounded (eg '' U) := by
    intro hb
    apply hUb
    apply ((hb.isCompact_closure.image eg.symm.continuous).isBounded).subset
    intro z hz
    exact ⟨eg z, subset_closure ⟨z, hz, rfl⟩, eg.symm_apply_apply z⟩
  have hc : c = 0 := by
    by_cases hc : c = 0
    · exact hc
    let p : ℂ := -d / c
    have hD : ¬ Bornology.IsBounded ((eg '' U) \ {p}) := by
      intro hb
      apply himg
      apply (hb.union (isCompact_singleton (x := p)).isBounded).subset
      intro z hz
      by_cases hp : z = p
      · exact Or.inr hp
      · exact Or.inl ⟨hz, hp⟩
    apply cml_denominator_zero (eg.symm.trans ef) hD
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hz.1
    change ef (eg.symm (eg x)) = _
    rw [eg.symm_apply_apply]
    apply hM x hx (hfa x hx) (hga x hx)
    intro he
    apply hz.2
    change eg x = -d / c
    apply (eq_div_iff hc).2
    linear_combination he
  have hd : d ≠ 0 := by
    intro hd
    exact hdet (by simp [hc, hd])
  have he : ∀ z ∈ U, ef z = (a * eg z + b) / d := by
    intro z hz
    simpa only [hc, zero_mul, zero_add] using
      hM z hz (hfa z hz) (hga z hz) (by simpa [hc] using hd)
  have hb : b = 0 := by
    have hh := he 0 h0
    rw [hf.2.2.1, hg.2.2.1] at hh
    have hh' : b / d = 0 := by simpa using hh.symm
    exact (div_eq_zero_iff.mp hh').resolve_right hd
  have ha : a = d := by
    have hh := he 1 h1
    rw [hf.2.2.2, hg.2.2.2, hb] at hh
    have hh' : a / d = 1 := by simpa using hh.symm
    exact (div_eq_one_iff_eq hd).mp hh'
  intro z hz
  rw [he z hz, hb, ha]
  field_simp
  simp

-- L5
/-- Normalized QC families with vanishing relative Schwarzian have actual relative jet limits. -/
theorem crbl_relative_jets_of_schwarzian {F G : ℕ → ℂ → ℂ} {K L : ℝ} {U : Set ℂ}
    (hU : IsOpen U) (hUc : IsConnected U) (hUb : ¬ Bornology.IsBounded U)
    (h0 : (0 : ℂ) ∈ U) (h1 : (1 : ℂ) ∈ U)
    (hF : ∀ n, IsKQCNormalizedPlane (F n) K)
    (hG : ∀ n, IsKQCNormalizedPlane (G n) L)
    (hlocal : ∀ z ∈ U, ∃ r > 0, ball z r ⊆ U ∧ ∀ᶠ n in atTop,
      DifferentiableOn ℂ (F n) (ball z r) ∧ DifferentiableOn ℂ (G n) (ball z r))
    (hS : ∀ z ∈ U, Tendsto (fun n => schwarzianHol (G n) z - schwarzianHol (F n) z)
      atTop (𝓝 0)) :
    Tendsto (fun n => crbl_relative_first (F n) (G n)) atTop (𝓝 1) ∧
    Tendsto (fun n => crbl_relative_second (F n) (G n)) atTop (𝓝 0) := by
  have ht : Tendsto (fun n => (crbl_relative_first (F n) (G n),
      crbl_relative_second (F n) (G n))) atTop (𝓝 ((1 : ℂ), (0 : ℂ))) := by
    apply Filter.tendsto_of_subseq_tendsto
    intro ns hns
    obtain ⟨ms, hms, f, g, hf, hg, hFl, hGl⟩ :=
      crbl_common_subseq (fun n => hF (ns n)) (fun n => hG (ns n))
    let ι : ℕ → ℕ := fun n => ns (ms n)
    have hι : Tendsto ι atTop atTop := hns.comp hms.tendsto_atTop
    have hlocalF : ∀ z ∈ U, ∃ r > 0, ball z r ⊆ U ∧
        ∀ᶠ n in atTop, DifferentiableOn ℂ (F (ι n)) (ball z r) := by
      intro z hz
      obtain ⟨r, hr, hs, hh⟩ := hlocal z hz
      exact ⟨r, hr, hs, hι.eventually (hh.mono (fun n hn => hn.1))⟩
    have hlocalG : ∀ z ∈ U, ∃ r > 0, ball z r ⊆ U ∧
        ∀ᶠ n in atTop, DifferentiableOn ℂ (G (ι n)) (ball z r) := by
      intro z hz
      obtain ⟨r, hr, hs, hh⟩ := hlocal z hz
      exact ⟨r, hr, hs, hι.eventually (hh.mono (fun n hn => hn.2))⟩
    obtain ⟨hfd, hFj⟩ := crbl_local_jets
      (hFl.tendstoLocallyUniformlyOn.mono (subset_univ U)) hlocalF
    obtain ⟨hgd, hGj⟩ := crbl_local_jets
      (hGl.tendstoLocallyUniformlyOn.mono (subset_univ U)) hlocalG
    have hfi : InjOn f U := hf.1.2.2.1.2.1.mono (subset_univ U)
    have hgi : InjOn g U := hg.1.2.2.1.2.1.mono (subset_univ U)
    have hSeq : ∀ z ∈ U, schwarzianHol f z = schwarzianHol g z := by
      intro z hz
      obtain ⟨r, hr, hs, hh⟩ := hlocal z hz
      have hFa : ∀ᶠ n in atTop, AnalyticAt ℂ (F (ι n)) z :=
        hι.eventually (hh.mono (fun n hn => hn.1.analyticOnNhd isOpen_ball z (mem_ball_self hr)))
      have hGa : ∀ᶠ n in atTop, AnalyticAt ℂ (G (ι n)) z :=
        hι.eventually (hh.mono (fun n hn => hn.2.analyticOnNhd isOpen_ball z (mem_ball_self hr)))
      have hSF := crbl_schwarzian_tendsto hFa (hfd.analyticOnNhd hU z hz)
        (hFj z hz).1 (hFj z hz).2.1 (hFj z hz).2.2 (deriv_ne_zero_of_injOn hU hfd hfi hz)
      have hSG := crbl_schwarzian_tendsto hGa (hgd.analyticOnNhd hU z hz)
        (hGj z hz).1 (hGj z hz).2.1 (hGj z hz).2.2 (deriv_ne_zero_of_injOn hU hgd hgi hz)
      exact (sub_eq_zero.mp (tendsto_nhds_unique (hSG.sub hSF) ((hS z hz).comp hι))).symm
    have he : f =ᶠ[𝓝 (0 : ℂ)] g :=
      Filter.eventuallyEq_of_mem (hU.mem_nhds h0)
        (crbl_rigidity hU hUc hUb h0 h1 hf hg hfd hgd hSeq)
    have he1 : deriv f 0 = deriv g 0 := he.deriv_eq
    have he2 : deriv (deriv f) 0 = deriv (deriv g) 0 := he.deriv.deriv_eq
    have hn : deriv f 0 ≠ 0 := deriv_ne_zero_of_injOn hU hfd hfi h0
    have hp : Tendsto (fun n => crbl_relative_first (F (ι n)) (G (ι n))) atTop (𝓝 1) := by
      have hh := (hGj 0 h0).1.div (hFj 0 h0).1 hn
      rw [← he1, div_self hn] at hh
      apply hh.congr'
      exact Eventually.of_forall (fun n => rfl)
    have hq : Tendsto (fun n => crbl_relative_second (F (ι n)) (G (ι n))) atTop (𝓝 0) := by
      have hh := (((hGj 0 h0).2.1.mul (hFj 0 h0).1).sub
        ((hGj 0 h0).1.mul (hFj 0 h0).2.1)).div ((hFj 0 h0).1.pow 3) (pow_ne_zero 3 hn)
      have hv : (deriv (deriv g) 0 * deriv f 0 - deriv g 0 * deriv (deriv f) 0) /
          (deriv f 0)^3 = 0 := by
        rw [← he1, ← he2]
        ring
      rw [hv] at hh
      apply hh.congr'
      exact Eventually.of_forall (fun n => rfl)
    exact ⟨ms, hp.prodMk_nhds hq⟩
  exact ⟨(continuous_fst.tendsto ((1 : ℂ), (0 : ℂ))).comp ht,
    (continuous_snd.tendsto ((1 : ℂ), (0 : ℂ))).comp ht⟩

-- L6
/-- The actual synchronized welding blowups have relative first jet tending to one
and relative second jet tending to zero. No limit-existence premise is assumed. -/
theorem crbl_actual_relative_jets {μ ν : LinfStar}
    (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall)
    (hP : AInf.toFun (bersPhi ν - bersPhi μ) ∈ A2fun unitDisc)
    (eμ eν : ℂ ≃ₜ ℂ) {K L : ℝ} (hK : IsKQC eμ univ K) (hL : IsKQC eν univ L)
    (heμ : EqOn eμ (fsans μ) unitDisc) (heν : EqOn eν (fsans ν) unitDisc)
    {a : ℕ → ℂ} (ha : ∀ n, 0 < ‖a n‖ ∧ ‖a n‖ < 1)
    (halim : Tendsto (fun n => ‖a n‖) atTop (𝓝 1)) :
    Tendsto (fun n => crbl_relative_first (cbl_normalized eμ (a n))
      (cbl_normalized eν (a n))) atTop (𝓝 1) ∧
    Tendsto (fun n => crbl_relative_second (cbl_normalized eμ (a n))
      (cbl_normalized eν (a n))) atTop (𝓝 0) := by
  let U : Set ℂ := {t : ℂ | -2 < t.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have h0 : (0 : ℂ) ∈ U := by norm_num [U]
  have h1 : (1 : ℂ) ∈ U := by norm_num [U]
  have hUc : IsConnected U := (convex_halfSpace_re_gt (-2)).isConnected ⟨0, h0⟩
  have hUb : ¬ Bornology.IsBounded U := by
    intro hb
    obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hb
    have hx : ((|R| + 1 : ℝ) : ℂ) ∈ U := by
      change -2 < |R| + 1
      linarith [abs_nonneg R]
    have hh := hR _ hx
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < |R| + 1)] at hh
    linarith [le_abs_self R]
  refine crbl_relative_jets_of_schwarzian hU hUc hUb h0 h1
    (fun n => cbl_normalized_plane eμ hK (ha n).1 (ha n).2)
    (fun n => cbl_normalized_plane eν hL (ha n).1 (ha n).2) ?_ ?_
  · intro z hz
    obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.mp hU z hz
    have hC : closedBall z (r/2) ⊆ U := by
      intro w hw
      exact hb (mem_ball.mpr ((mem_closedBall.mp hw).trans_lt (half_lt_self hr)))
    refine ⟨r/2, half_pos hr, ball_subset_closedBall.trans hC, ?_⟩
    filter_upwards [cbs_eventually_mapsTo ha halim (isCompact_closedBall z (r/2)) hC] with n hn
    exact ⟨(cbs_normalized_holomorphic hμ eμ heμ (ha n).1 (ha n).2).mono
      (fun w hw => hn (ball_subset_closedBall hw)),
      (cbs_normalized_holomorphic hν eν heν (ha n).1 (ha n).2).mono
      (fun w hw => hn (ball_subset_closedBall hw))⟩
  · intro z hz
    have ht := (cbs_scaled_tendsto_locallyUniformlyOn ha halim hP).tendsto_at hz
    apply ht.congr'
    filter_upwards [cbs_eventually_mapsTo ha halim (isCompact_singleton (x := z))
      (singleton_subset_iff.mpr hz)] with n hn
    exact (cbs_schwarzian_difference hμ hν eμ eν heμ heν (ha n).1 (ha n).2
      (hn (mem_singleton z))).symm

end TakhtajanTeo
