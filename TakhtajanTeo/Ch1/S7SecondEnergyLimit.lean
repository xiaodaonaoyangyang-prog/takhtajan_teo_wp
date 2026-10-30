import TakhtajanTeo.Ch1.S7CompactGraphBound
import TakhtajanTeo.Ch1.S7WeightedPairingContinuity
import TakhtajanTeo.Ch1.S7SecondGraphNorm

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- The actual second differential of the cutoff is eventually the original germ. -/
theorem s7el_eventually_q_eq (h : ℂ → ℂ) {z : ℂ} (hz : z ∈ unitDisc) :
    ∀ᶠ n : ℕ in atTop,
      s7et_q (fun w => (s7dc_cutoff n w : ℂ)*h w) z = s7et_q h z := by
  filter_upwards [s7dc_eventually_one hz] with n hn
  apply s7et_q_congr
  filter_upwards [hn] with w hw
  simp only [hw, Complex.ofReal_one, one_mul]

theorem s7el_q_measurable (h : ℂ → ℂ) : Measurable (s7et_q h) :=
  measurable_dzbar _

theorem s7el_laplace_measurable (h : ℂ → ℂ) : Measurable (laplace0 h) := by
  have hr : Measurable (fun z : ℂ => (rho z : ℂ)⁻¹) := by unfold rho; fun_prop
  exact (hr.mul (measurable_dz _)).neg

theorem s7el_q_pointwise (h : ℂ → ℂ) :
    ∀ᵐ z ∂(volume.restrict unitDisc),
      Tendsto (fun n : ℕ => s7et_q (fun w => (s7dc_cutoff n w : ℂ)*h w) z)
        atTop (𝓝 (s7et_q h z)) := by
  filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
  exact (tendsto_congr' (s7el_eventually_q_eq h hz)).2 tendsto_const_nhds

/-- Fatou identifies a raw pointwise limit of a weighted-norm Cauchy sequence.
No finite norm or abstract closedness of the differential is assumed. -/
theorem s7el_cauchy_pointwise_limit {D : Set ℂ} {q : ℕ → ℂ → ℂ} {Q : ℂ → ℂ}
    (hq : ∀ n, AEStronglyMeasurable (q n) (volume.restrict D))
    (hQ : AEStronglyMeasurable Q (volume.restrict D))
    (hp : ∀ᵐ z ∂(volume.restrict D), Tendsto (fun n => q n z) atTop (𝓝 (Q z)))
    (hc : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      normL2 D (fun z => q n z-q m z) ≤ ε) :
    Tendsto (fun n => normL2 D (fun z => q n z-Q z)) atTop (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.2
  intro ε hε
  obtain ⟨N,hN⟩ := hc ε hε
  filter_upwards [eventually_ge_atTop N] with n hn
  have hp' : ∀ᵐ z ∂(volume.restrict D),
      Tendsto (fun m => q n z-q m z) atTop (𝓝 (q n z-Q z)) := by
    filter_upwards [hp] with z hz
    exact tendsto_const_nhds.sub hz
  exact (s7pc_normL2_fatou (fun m => (hq n).sub (hq m)) ((hq n).sub hQ) hp').trans
    (liminf_le_of_frequently_le' ((eventually_ge_atTop N).mono (fun m hm => hN n hn m hm)).frequently)

theorem s7el_norm_sub_le {D : Set ℂ} {f g : ℂ → ℂ}
    (hf : AEStronglyMeasurable f (volume.restrict D))
    (hg : AEStronglyMeasurable g (volume.restrict D)) :
    normL2 D (fun z => f z-g z) ≤ normL2 D f+normL2 D g := by
  rw [grp_normL2_eq D (f := fun z => f z-g z) (hf.sub hg), grp_normL2_eq _ hf, grp_normL2_eq _ hg]
  exact eLpNorm_sub_le (by norm_num)

/-- Graph convergence and the proved difference bound imply weighted-norm Cauchy.
This is the limit argument only; the actual differential estimate is supplied
by the compact second-energy theorem. -/
theorem s7el_cauchy_of_graph {D : Set ℂ} {a b q : ℕ → ℂ → ℂ} {A B : ℂ → ℂ}
    (ha : ∀ n, AEStronglyMeasurable (a n) (volume.restrict D))
    (hb : ∀ n, AEStronglyMeasurable (b n) (volume.restrict D))
    (hA : AEStronglyMeasurable A (volume.restrict D))
    (hB : AEStronglyMeasurable B (volume.restrict D))
    (hga : Tendsto (fun n => normL2 D (fun z => a n z-A z)) atTop (𝓝 0))
    (hgb : Tendsto (fun n => normL2 D (fun z => b n z-B z)) atTop (𝓝 0))
    (hbound : ∀ n m, normL2 D (fun z => q n z-q m z) ≤
      2*(normL2 D (fun z => a n z-a m z)+normL2 D (fun z => b n z-b m z))) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      normL2 D (fun z => q n z-q m z) ≤ ε := by
  intro ε hε
  have hd : 0 < ε/8 := ENNReal.div_pos hε.ne' (by norm_num)
  obtain ⟨Na,hNa⟩ := eventually_atTop.1 (ENNReal.tendsto_nhds_zero.1 hga (ε/8) hd)
  obtain ⟨Nb,hNb⟩ := eventually_atTop.1 (ENNReal.tendsto_nhds_zero.1 hgb (ε/8) hd)
  refine ⟨max Na Nb, fun n hn m hm => ?_⟩
  have haa : normL2 D (fun z => a n z-a m z) ≤ ε/8+ε/8 := by
    have ht := s7el_norm_sub_le ((ha n).sub hA) ((ha m).sub hA)
    simp only [Pi.sub_apply, sub_sub_sub_cancel_right] at ht
    exact ht.trans (add_le_add (hNa n (le_trans (le_max_left _ _) hn))
      (hNa m (le_trans (le_max_left _ _) hm)))
  have hbb : normL2 D (fun z => b n z-b m z) ≤ ε/8+ε/8 := by
    have ht := s7el_norm_sub_le ((hb n).sub hB) ((hb m).sub hB)
    simp only [Pi.sub_apply, sub_sub_sub_cancel_right] at ht
    exact ht.trans (add_le_add (hNb n (le_trans (le_max_right _ _) hn))
      (hNb m (le_trans (le_max_right _ _) hm)))
  calc
    _ ≤ 2*((ε/8+ε/8)+(ε/8+ε/8)) :=
      (hbound n m).trans (mul_le_mul' le_rfl (add_le_add haa hbb))
    _ = (ε/8)*8 := by ring
    _ = ε := ENNReal.div_mul_cancel (by norm_num) (by norm_num)

/-- A finite approximant and convergence in the raw weighted norm imply
finiteness of the identified pointwise limit. -/
theorem s7el_limit_finite {D : Set ℂ} {q : ℕ → ℂ → ℂ} {Q : ℂ → ℂ}
    (hq : ∀ n, AEStronglyMeasurable (q n) (volume.restrict D))
    (hQ : AEStronglyMeasurable Q (volume.restrict D))
    (hqn : ∀ n, normL2 D (q n) < ∞)
    (hc : Tendsto (fun n => normL2 D (fun z => q n z-Q z)) atTop (𝓝 0)) :
    normL2 D Q < ∞ := by
  obtain ⟨n,hn⟩ := (ENNReal.tendsto_nhds_zero.1 hc 1 (by norm_num)).exists
  have hb := s7el_norm_sub_le (hq n) ((hq n).sub hQ)
  simp only [Pi.sub_apply, sub_sub_cancel] at hb
  exact hb.trans_lt (ENNReal.add_lt_top.2 ⟨hqn n, hn.trans_lt (by simp)⟩)

/-- The actual second differential has finite energy and is the weighted L2
limit of the explicit compact cutoff differentials. Only h and its Laplacian
are assumed to have finite weighted norm. -/
theorem s7el_q_convergence {h : ℂ → ℂ}
    (hh : ContDiffOn ℝ (⊤ : ℕ∞) h unitDisc)
    (hL : normL2 unitDisc h < ∞) (hDL : normL2 unitDisc (laplace0 h) < ∞) :
    normL2 unitDisc (s7et_q h) < ∞ ∧
    Tendsto (fun n : ℕ => normL2 unitDisc (fun z =>
      s7et_q (fun w => (s7dc_cutoff n w : ℂ)*h w) z-s7et_q h z)) atTop (𝓝 0) := by
  obtain ⟨hk,hkh,hkl⟩ := s7ga_graph_approximation hh hL hDL
  let k : ℕ → ℂ → ℂ := fun n z => (s7dc_cutoff n z : ℂ)*h z
  have hkm (n : ℕ) : AEStronglyMeasurable (k n) (volume.restrict unitDisc) :=
    (hk n).1.continuous.aestronglyMeasurable
  have hlm (n : ℕ) : AEStronglyMeasurable (laplace0 (k n)) (volume.restrict unitDisc) :=
    (s7el_laplace_measurable _).aestronglyMeasurable
  have hqm (n : ℕ) : AEStronglyMeasurable (s7et_q (k n)) (volume.restrict unitDisc) :=
    (s7el_q_measurable _).aestronglyMeasurable
  have hQ : AEStronglyMeasurable (s7et_q h) (volume.restrict unitDisc) :=
    (s7el_q_measurable _).aestronglyMeasurable
  have hconv : Tendsto (fun n => normL2 unitDisc (fun z =>
      s7et_q (k n) z-s7et_q h z)) atTop (𝓝 0) := by
    apply s7el_cauchy_pointwise_limit hqm hQ (s7el_q_pointwise h)
    apply s7el_cauchy_of_graph hlm hkm (s7el_laplace_measurable h).aestronglyMeasurable
      (hh.continuousOn.aestronglyMeasurable measurableSet_ball) hkl hkh
    intro n m
    exact (s7gn_graph_norm_sub (hk n).1 (hk m).1 (hk n).2.1 (hk m).2.1
      (hk n).2.2 (hk m).2.2).2
  refine ⟨s7el_limit_finite hqm hQ (fun n => ?_) hconv, hconv⟩
  exact (s7gn_graph_norm_bound (hk n).1 (hk n).2.1 (hk n).2.2).1

end TakhtajanTeo
