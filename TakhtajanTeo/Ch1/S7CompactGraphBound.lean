import TakhtajanTeo.Ch1.S7GraphApproximation
import TakhtajanTeo.Ch1.S7ExteriorEnergyTransport

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem s7gb_laplace_smooth {h : ℂ → ℂ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    ContDiff ℝ (⊤ : ℕ∞) (laplace0 h) := by
  have hd : ContDiff ℝ (⊤ : ℕ∞) (dz (dzbar h)) := by
    rw [← contDiffOn_univ]
    exact wp_contDiffOn_dz (s7ca_dzbar_smooth hh).contDiffOn isOpen_univ (by simp)
  exact ((wp_rho_inv_contDiff.of_le le_top).mul hd).neg

theorem s7gb_laplace_support (h : ℂ → ℂ) : tsupport (laplace0 h) ⊆ tsupport h := by
  apply closure_minimal _ (isClosed_tsupport h)
  intro z hz
  by_contra hn
  have hdb : z ∉ tsupport (dzbar h) := fun ht => hn (s7ca_dzbar_support h ht)
  apply hz
  simp only [laplace0, dz, sp_fderiv_eq_zero_of_notMem_tsupport hdb,
    mul_zero, sub_self, zero_div, neg_zero]

theorem s7gb_q_support (h : ℂ → ℂ) : tsupport (s7et_q h) ⊆ tsupport h := by
  exact (s7ca_dzbar_support _).trans
    (tsupport_mul_subset_right.trans (s7ca_dzbar_support h))

/-- Genuine compact self-adjointness, with both complex weighted pairings integrable. -/
theorem s7gb_self_adjoint {h k : ℂ → ℂ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hk : ContDiff ℝ (⊤ : ℕ∞) k)
    (hc : HasCompactSupport h) (kc : HasCompactSupport k)
    (hs : tsupport h ⊆ unitDisc) (ks : tsupport k ⊆ unitDisc) :
    Integrable (fun z => h z*conj (laplace0 k z)*(rho z : ℂ)) ∧
    Integrable (fun z => laplace0 h z*conj (k z)*(rho z : ℂ)) ∧
    (∫ z, h z*conj (laplace0 k z)*(rho z : ℂ)) =
      ∫ z, laplace0 h z*conj (k z)*(rho z : ℂ) := by
  obtain ⟨hI,hJ,hG⟩ := s7cg_green (Or.inl rfl) (hk.of_le (by simp)).contDiffOn
    (hh.of_le (by simp)) hc hs
  obtain ⟨kI,kJ,kG⟩ := s7cg_green (Or.inl rfl) (hh.of_le (by simp)).contDiffOn
    (hk.of_le (by simp)) kc ks
  have hR : Integrable (fun z => laplace0 h z*conj (k z)*(rho z : ℂ)) := by
    apply (Complex.conjCLE.toContinuousLinearMap.integrable_comp kI).congr
    apply Filter.Eventually.of_forall
    intro z
    change conj (k z*conj (laplace0 h z)*(rho z : ℂ)) = _
    simp only [map_mul, conj_conj, Complex.conj_ofReal]
    ring
  refine ⟨hI,hR,?_⟩
  calc
    _ = ∫ z, dzbar h z*conj (dzbar k z) := hG
    _ = conj (∫ z, dzbar k z*conj (dzbar h z)) := by
      rw [← integral_conj]
      apply integral_congr_ae
      filter_upwards with z
      simp only [map_mul, conj_conj]
      ring
    _ = conj (∫ z, k z*conj (laplace0 h z)*(rho z : ℂ)) := congrArg conj kG.symm
    _ = _ := by
      rw [← integral_conj]
      apply integral_congr_ae
      filter_upwards with z
      simp only [map_mul, conj_conj, Complex.conj_ofReal]
      ring

private theorem real_energy_of_pair {h : ℂ → ℂ}
    (hi : Integrable (fun z => h z*conj (h z)*(rho z : ℂ))) :
    Integrable (fun z => ‖h z‖^2*rho z) := by
  apply hi.re.congr
  filter_upwards with z
  change (h z*conj (h z)*(rho z : ℂ)).re = _
  simp only [Complex.mul_conj, ← Complex.ofReal_mul, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq]

theorem s7gb_compact_energy_integrable {h : ℂ → ℂ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hc : HasCompactSupport h)
    (hs : tsupport h ⊆ unitDisc) : Integrable (fun z => ‖h z‖^2*rho z) := by
  have hF : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => conj (h z)*(rho z : ℂ)) unitDisc :=
    (Complex.conjCLE.toContinuousLinearMap.contDiff.comp hh).contDiffOn.mul
      (wp_rho_contDiffOn.of_le le_top)
  have hp : Continuous (fun z => h z*(conj (h z)*(rho z : ℂ))) :=
    (sp_contDiff_mul isOpen_ball hF hh hs).continuous
  have hpc : HasCompactSupport (fun z => h z*(conj (h z)*(rho z : ℂ))) := hc.mul_right
  have hi := hp.integrable_of_hasCompactSupport (μ := volume) hpc
  apply real_energy_of_pair
  simpa only [mul_assoc] using hi

/-- The compact second identity reduced to h and its actual Laplacian. -/
theorem s7gb_reduced_energy {h : ℂ → ℂ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hc : HasCompactSupport h)
    (hs : tsupport h ⊆ unitDisc) :
    Integrable (fun z => s7et_q h z*conj (s7et_q h z)*(rho z : ℂ)) ∧
    Integrable (fun z => laplace0 h z*conj (laplace0 h z+(1/2:ℂ)*h z)*(rho z : ℂ)) ∧
    (∫ z, s7et_q h z*conj (s7et_q h z)*(rho z : ℂ)) =
      ∫ z, laplace0 h z*conj (laplace0 h z+(1/2:ℂ)*h z)*(rho z : ℂ) := by
  let k : ℂ → ℂ := fun z => laplace0 h z+(1/2:ℂ)*h z
  have hl := s7gb_laplace_smooth hh
  have hlc : HasCompactSupport (laplace0 h) :=
    hc.of_isClosed_subset (isClosed_tsupport _) (s7gb_laplace_support h)
  have hk : ContDiff ℝ (⊤ : ℕ∞) k := hl.add (contDiff_const.mul hh)
  have hkc : HasCompactSupport k := hlc.add hc.mul_left
  have hks : tsupport k ⊆ unitDisc :=
    (tsupport_binop_subset (· + ·) (add_zero (0 : ℂ)) _ _).trans (union_subset ((s7gb_laplace_support h).trans hs)
      (tsupport_mul_subset_right.trans hs))
  obtain ⟨hq,_,he⟩ := s7ca_second_energy hh hc hs
  obtain ⟨_,hR,hG⟩ := s7gb_self_adjoint hh hk hc hkc hs hks
  exact ⟨hq,hR,he.trans hG⟩

private theorem real_pair_bound (u v : ℂ) :
    (u*conj (u+(1/2:ℂ)*v)).re ≤ 2*(‖u‖^2+‖v‖^2) := by
  simp [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  nlinarith [sq_nonneg (u.re-v.re),sq_nonneg (u.im-v.im),
    sq_nonneg u.re,sq_nonneg u.im,sq_nonneg v.re,sq_nonneg v.im]

/-- A genuine compact bound of the second differential by the weighted graph energy. -/
theorem s7gb_graph_bound {h : ℂ → ℂ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hc : HasCompactSupport h)
    (hs : tsupport h ⊆ unitDisc) :
    Integrable (fun z => ‖s7et_q h z‖^2*rho z) ∧
    (∫ z, ‖s7et_q h z‖^2*rho z) ≤
      2*((∫ z, ‖laplace0 h z‖^2*rho z)+(∫ z, ‖h z‖^2*rho z)) := by
  obtain ⟨hq,hR,he⟩ := s7gb_reduced_energy hh hc hs
  have hQ := real_energy_of_pair hq
  have hH := s7gb_compact_energy_integrable hh hc hs
  have hlc : HasCompactSupport (laplace0 h) :=
    hc.of_isClosed_subset (isClosed_tsupport _) (s7gb_laplace_support h)
  have hD := s7gb_compact_energy_integrable (s7gb_laplace_smooth hh) hlc
    ((s7gb_laplace_support h).trans hs)
  have hpoint (z : ℂ) :
      (laplace0 h z*conj (laplace0 h z+(1/2:ℂ)*h z)*(rho z : ℂ)).re ≤
      2*(‖laplace0 h z‖^2*rho z+‖h z‖^2*rho z) := by
    have hr : 0 ≤ rho z := by unfold rho; positivity
    have hb := mul_le_mul_of_nonneg_right (real_pair_bound (laplace0 h z) (h z)) hr
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    nlinarith [hb]
  have hi := integral_mono hR.re ((hD.add hH).const_mul 2) hpoint
  simp only [Pi.add_apply] at hi
  rw [integral_re hR, ← he] at hi
  rw [← integral_re hq] at hi
  have heq : (fun z => (s7et_q h z*conj (s7et_q h z)*(rho z : ℂ)).re) =
      (fun z => ‖s7et_q h z‖^2*rho z) := by
    funext z
    simp only [Complex.mul_conj, ← Complex.ofReal_mul, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq]
  change (∫ z, (s7et_q h z*conj (s7et_q h z)*(rho z : ℂ)).re) ≤ _ at hi
  rw [heq, integral_const_mul, integral_add hD hH] at hi
  exact ⟨hQ,hi⟩

end TakhtajanTeo
