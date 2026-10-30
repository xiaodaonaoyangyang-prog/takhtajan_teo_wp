import TakhtajanTeo.Ch1.S7CompactGraphBound
import TakhtajanTeo.Ch1.S7WeightedPairingContinuity

/-! Actual compact second-differential graph estimates in normL2.
The integral identity is reused; the norm and support bridges are proved. -/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

private theorem s7gn_dz_sub {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    dz (fun w => f w - g w) z = dz f z - dz g z := by
  unfold dz
  rw [fderiv_fun_sub hf hg]
  simp only [sub_apply]
  ring

/-- Global smoothness of the actual weighted second derivative. -/
theorem s7gn_q_smooth {h : ℂ → ℂ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    ContDiff ℝ (⊤ : ℕ∞) (s7et_q h) :=
  s7ca_dzbar_smooth ((wp_rho_inv_contDiff.of_le le_top).mul (s7ca_dzbar_smooth hh))

/-- The actual second differential commutes with subtraction. -/
theorem s7gn_q_sub {h k : ℂ → ℂ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hk : ContDiff ℝ (⊤ : ℕ∞) k) :
    s7et_q (fun z => h z - k z) = fun z => s7et_q h z - s7et_q k z := by
  have hd : dzbar (fun z => h z - k z) = fun z => dzbar h z - dzbar k z := by
    funext z
    exact wp_dzbar_sub (hh.differentiable (by simp) z) (hk.differentiable (by simp) z)
  have ha : ContDiff ℝ (⊤ : ℕ∞) (fun z => (rho z : ℂ)⁻¹ * dzbar h z) :=
    (wp_rho_inv_contDiff.of_le le_top).mul (s7ca_dzbar_smooth hh)
  have hb : ContDiff ℝ (⊤ : ℕ∞) (fun z => (rho z : ℂ)⁻¹ * dzbar k z) :=
    (wp_rho_inv_contDiff.of_le le_top).mul (s7ca_dzbar_smooth hk)
  have he : (fun z => (rho z : ℂ)⁻¹ * dzbar (fun w => h w - k w) z) =
      (fun z => (rho z : ℂ)⁻¹ * dzbar h z - (rho z : ℂ)⁻¹ * dzbar k z) := by
    rw [hd]
    funext z
    ring
  funext z
  unfold s7et_q
  rw [he]
  exact wp_dzbar_sub (ha.differentiable (by simp) z) (hb.differentiable (by simp) z)

/-- The actual hyperbolic Laplacian commutes with subtraction. -/
theorem s7gn_laplace_sub {h k : ℂ → ℂ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hk : ContDiff ℝ (⊤ : ℕ∞) k) :
    laplace0 (fun z => h z - k z) = fun z => laplace0 h z - laplace0 k z := by
  have hd : dzbar (fun z => h z - k z) = fun z => dzbar h z - dzbar k z := by
    funext z
    exact wp_dzbar_sub (hh.differentiable (by simp) z) (hk.differentiable (by simp) z)
  funext z
  unfold laplace0
  rw [hd, s7gn_dz_sub ((s7ca_dzbar_smooth hh).differentiable (by simp) z)
    ((s7ca_dzbar_smooth hk).differentiable (by simp) z)]
  ring

/-- Support containment identifies the genuine plane and domain energies. -/
theorem s7gn_plane_energy_eq {D : Set ℂ} {f : ℂ → ℂ} (hs : tsupport f ⊆ D) :
    (∫ z, ‖f z‖ ^ 2 * rho z) = ∫ z in D, ‖f z‖ ^ 2 * rho z := by
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  rw [image_eq_zero_of_notMem_tsupport (fun ht => hz (hs ht))]
  simp

/-- Squaring the actual ENNReal norm recovers its defining lower integral. -/
theorem s7gn_normL2_sq (D : Set ℂ) (f : ℂ → ℂ) :
    normL2 D f ^ 2 = ∫⁻ z in D, (‖f z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z) := by
  unfold normL2
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- For an integrable energy density, the squared norm is the ofReal of
the actual energy integral. -/
theorem s7gn_normL2_sq_integral {D : Set ℂ} {f : ℂ → ℂ}
    (hi : Integrable (fun z => ‖f z‖ ^ 2 * rho z) (volume.restrict D)) :
    normL2 D f ^ 2 = ENNReal.ofReal (∫ z in D, ‖f z‖ ^ 2 * rho z) := by
  rw [s7gn_normL2_sq, ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (by unfold rho; positivity))]
  apply lintegral_congr
  intro z
  rw [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow (norm_nonneg _)]
  simp only [ofReal_norm, enorm_eq_nnnorm]

theorem s7gn_normL2_finite_of_energy {D : Set ℂ} {f : ℂ → ℂ}
    (hi : Integrable (fun z => ‖f z‖ ^ 2 * rho z) (volume.restrict D)) :
    normL2 D f < ∞ := by
  have hs : normL2 D f ^ 2 < ∞ := by
    rw [s7gn_normL2_sq_integral hi]
    exact ENNReal.ofReal_lt_top
  simpa only [ENNReal.pow_lt_top_iff, OfNat.ofNat_ne_zero, or_false] using hs

theorem s7gn_energy_eq_sq {D : Set ℂ} {f : ℂ → ℂ}
    (hi : Integrable (fun z => ‖f z‖ ^ 2 * rho z) (volume.restrict D)) :
    (∫ z in D, ‖f z‖ ^ 2 * rho z) = (normL2 D f).toReal ^ 2 := by
  have hp : 0 ≤ ∫ z in D, ‖f z‖ ^ 2 * rho z :=
    integral_nonneg (fun z => mul_nonneg (sq_nonneg _) (by unfold rho; positivity))
  have he := congrArg ENNReal.toReal (s7gn_normL2_sq_integral hi)
  simpa only [ENNReal.toReal_pow, ENNReal.toReal_ofReal hp] using he.symm

/-- Compact test functions have finite actual weighted norm. -/
theorem s7gn_compact_normL2_finite {h : ℂ → ℂ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hc : HasCompactSupport h)
    (hs : tsupport h ⊆ unitDisc) : normL2 unitDisc h < ∞ :=
  s7gn_normL2_finite_of_energy (s7gb_compact_energy_integrable hh hc hs).integrableOn

/-- The compact graph energy bound implies a finite ENNReal norm bound for
the actual q. No norm/integral bridge is assumed. -/
theorem s7gn_graph_norm_bound {h : ℂ → ℂ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hc : HasCompactSupport h)
    (hs : tsupport h ⊆ unitDisc) :
    normL2 unitDisc (s7et_q h) < ∞ ∧
      normL2 unitDisc (s7et_q h) ≤ 2 * (normL2 unitDisc (laplace0 h) + normL2 unitDisc h) := by
  obtain ⟨hqI, hbound⟩ := s7gb_graph_bound hh hc hs
  have hlc : HasCompactSupport (laplace0 h) :=
    hc.of_isClosed_subset (isClosed_tsupport _) (s7gb_laplace_support h)
  have hls : tsupport (laplace0 h) ⊆ unitDisc := (s7gb_laplace_support h).trans hs
  have hqs : tsupport (s7et_q h) ⊆ unitDisc := (s7gb_q_support h).trans hs
  have hlI := s7gb_compact_energy_integrable (s7gb_laplace_smooth hh) hlc hls
  have hhI := s7gb_compact_energy_integrable hh hc hs
  have hqfin : normL2 unitDisc (s7et_q h) < ∞ := s7gn_normL2_finite_of_energy hqI.integrableOn
  have hlfin : normL2 unitDisc (laplace0 h) < ∞ := s7gn_normL2_finite_of_energy hlI.integrableOn
  have hhfin : normL2 unitDisc h < ∞ := s7gn_normL2_finite_of_energy hhI.integrableOn
  rw [s7gn_plane_energy_eq hqs, s7gn_plane_energy_eq hls, s7gn_plane_energy_eq hs,
    s7gn_energy_eq_sq hqI.integrableOn, s7gn_energy_eq_sq hlI.integrableOn,
    s7gn_energy_eq_sq hhI.integrableOn] at hbound
  refine ⟨hqfin, ?_⟩
  have hsum : 2 * (normL2 unitDisc (laplace0 h) + normL2 unitDisc h) ≠ ∞ := by
    exact (ENNReal.mul_lt_top (by norm_num) (ENNReal.add_lt_top.mpr ⟨hlfin, hhfin⟩)).ne
  apply (ENNReal.toReal_le_toReal hqfin.ne hsum).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.toReal_add hlfin.ne hhfin.ne]
  have hsq : (normL2 unitDisc (s7et_q h)).toReal ^ 2 ≤
      (2 * ((normL2 unitDisc (laplace0 h)).toReal + (normL2 unitDisc h).toReal)) ^ 2 := by
    nlinarith [mul_nonneg (ENNReal.toReal_nonneg (a := normL2 unitDisc (laplace0 h)))
      (ENNReal.toReal_nonneg (a := normL2 unitDisc h)),
      sq_nonneg (normL2 unitDisc (laplace0 h)).toReal, sq_nonneg (normL2 unitDisc h).toReal]
  exact le_of_sq_le_sq hsq (by positivity)

/-- The same graph norm bound applies to the actual difference of two
smooth compactly supported functions. -/
theorem s7gn_graph_norm_sub {h k : ℂ → ℂ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hk : ContDiff ℝ (⊤ : ℕ∞) k)
    (hc : HasCompactSupport h) (kc : HasCompactSupport k)
    (hs : tsupport h ⊆ unitDisc) (ks : tsupport k ⊆ unitDisc) :
    normL2 unitDisc (fun z => s7et_q h z - s7et_q k z) < ∞ ∧
      normL2 unitDisc (fun z => s7et_q h z - s7et_q k z) ≤
        2 * (normL2 unitDisc (fun z => laplace0 h z - laplace0 k z) +
          normL2 unitDisc (fun z => h z - k z)) := by
  have hsub : tsupport (fun z => h z - k z) ⊆ unitDisc :=
    (tsupport_binop_subset (· - ·) (sub_self (0 : ℂ)) h k).trans (union_subset hs ks)
  have hb := s7gn_graph_norm_bound (hh.sub hk) (hc.sub kc) hsub
  rw [s7gn_q_sub hh hk, s7gn_laplace_sub hh hk] at hb
  exact hb

end TakhtajanTeo
