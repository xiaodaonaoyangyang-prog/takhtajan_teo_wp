import TakhtajanTeo.Ch1.S7CompactGreen

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- The formal adjoint identity with genuine compact testing and both terms L1. -/
theorem s7ca_adjoint {D : Set ℂ} (hD : IsOpen D) {f g : ℂ → ℂ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiffOn ℝ 1 g D)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ D) :
    Integrable (fun z => dzbar f z * conj (g z)) ∧
    Integrable (fun z => f z * conj (dz g z)) ∧
    (∫ z, dzbar f z * conj (g z)) = -(∫ z, f z * conj (dz g z)) := by
  have hgc : ContDiffOn ℝ 1 (fun z => conj (g z)) D :=
    Complex.conjCLE.toContinuousLinearMap.contDiff.comp_contDiffOn hg
  obtain ⟨hI,hJ,he⟩ := s7cg_stokes hD hgc hf hc hs
  have ha : (fun z => f z * dzbar (fun w => conj (g w)) z) =
      (fun z => f z * conj (dz g z)) := by
    funext z
    by_cases hz : z ∈ D
    · rw [dzbar_conj ((hg.differentiableOn one_ne_zero z hz).differentiableAt (hD.mem_nhds hz))]
    · have h0 : f z = 0 := image_eq_zero_of_notMem_tsupport (fun hh => hz (hs hh))
      simp only [h0, zero_mul]
  have hb : (fun z => conj (g z) * dzbar f z) = (fun z => dzbar f z * conj (g z)) := by
    funext z
    exact mul_comm _ _
  rw [ha] at hI he
  rw [hb] at hJ he
  refine ⟨hJ,hI,?_⟩
  rw [he,neg_neg]

/-- Differentiation does not enlarge the support of a compact test. -/
theorem s7ca_dzbar_support (f : ℂ → ℂ) : tsupport (dzbar f) ⊆ tsupport f := by
  apply closure_minimal _ (isClosed_tsupport f)
  intro z hz
  by_contra hn
  apply hz
  simp only [dzbar, sp_fderiv_eq_zero_of_notMem_tsupport hn, mul_zero, add_zero, zero_div]

/-- C-infinity regularity of the actual antiholomorphic derivative. -/
theorem s7ca_dzbar_smooth {f : ℂ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (dzbar f) := by
  rw [← contDiffOn_univ]
  exact wp_contDiffOn_dzbar hf.contDiffOn isOpen_univ (by simp)

/-- The two compact adjoint steps and the actual Laplace factorization.
This is a compact energy identity, not yet the global resolvent energy limit. -/
theorem s7ca_second_energy {h : ℂ → ℂ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hc : HasCompactSupport h) (hs : tsupport h ⊆ unitDisc) :
    let q := dzbar (fun z => (rho z : ℂ)⁻¹ * dzbar h z)
    Integrable (fun z => q z * conj (q z) * (rho z : ℂ)) ∧
    Integrable (fun z => h z * conj (laplace0 (fun w => laplace0 h w + (1/2)*h w) z) * (rho z : ℂ)) ∧
    (∫ z, q z * conj (q z) * (rho z : ℂ)) =
      ∫ z, h z * conj (laplace0 (fun w => laplace0 h w + (1/2)*h w) z) * (rho z : ℂ) := by
  let a : ℂ → ℂ := fun z => (rho z : ℂ)⁻¹
  let v : ℂ → ℂ := fun z => a z * dzbar h z
  let q : ℂ → ℂ := dzbar v
  let k : ℂ → ℂ := fun z => (rho z : ℂ) * q z
  change Integrable (fun z => q z * conj (q z) * (rho z : ℂ)) ∧ _
  have ha : ContDiff ℝ (⊤ : ℕ∞) a := wp_rho_inv_contDiff.of_le le_top
  have hv : ContDiff ℝ (⊤ : ℕ∞) v := ha.mul (s7ca_dzbar_smooth hh)
  have hq : ContDiff ℝ (⊤ : ℕ∞) q := s7ca_dzbar_smooth hv
  have hk : ContDiffOn ℝ (⊤ : ℕ∞) k unitDisc :=
    (wp_rho_contDiffOn.of_le le_top).mul hq.contDiffOn
  have hdk : ContDiffOn ℝ (⊤ : ℕ∞) (dz k) unitDisc :=
    wp_contDiffOn_dz hk isOpen_ball (by simp)
  have hag : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => a z * dz k z) unitDisc :=
    ha.contDiffOn.mul hdk
  have hdc : HasCompactSupport (dzbar h) :=
    hc.of_isClosed_subset (isClosed_tsupport _) (s7ca_dzbar_support h)
  have hvc : HasCompactSupport v := hdc.mul_left
  have hvs : tsupport v ⊆ unitDisc :=
    tsupport_mul_subset_right.trans ((s7ca_dzbar_support h).trans hs)
  obtain ⟨hI1,hJ1,he1⟩ := s7ca_adjoint isOpen_ball (hv.of_le (by simp))
    (hk.of_le (by simp)) hvc hvs
  obtain ⟨hI2,hJ2,he2⟩ := s7ca_adjoint isOpen_ball (hh.of_le (by simp))
    (hag.of_le (by simp)) hc hs
  have eL : (fun z => q z * conj (q z) * (rho z : ℂ)) =
      (fun z => q z * conj (k z)) := by
    funext z
    simp only [k,map_mul,Complex.conj_ofReal]
    ring
  have eM : (fun z => v z * conj (dz k z)) =
      (fun z => dzbar h z * conj (a z * dz k z)) := by
    funext z
    simp only [v,a,map_mul,map_inv₀,Complex.conj_ofReal]
    ring
  have eR : (fun z => h z * conj (dz (fun w => a w * dz k w) z)) =
      (fun z => h z * conj (laplace0 (fun w => laplace0 h w + (1/2)*h w) z) * (rho z : ℂ)) := by
    funext z
    by_cases hz : z ∈ unitDisc
    · have hr : (rho z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
        (rho_pos_of_norm_ne_one (ne_of_lt (by simpa [unitDisc,mem_ball,dist_zero_right] using hz))).ne'
      have hfac : a z * dz (fun w => a w * dz k w) z =
          laplace0 (fun w => laplace0 h w + (1/2)*h w) z :=
        laplace_factorization hh.contDiffOn hz
      have hdz : dz (fun w => a w * dz k w) z =
          (rho z : ℂ) * laplace0 (fun w => laplace0 h w + (1/2)*h w) z := by
        have ht := congrArg (fun x : ℂ => (rho z : ℂ)*x) hfac
        simpa only [a,← mul_assoc,mul_inv_cancel₀ hr,one_mul] using ht
      rw [hdz,map_mul,Complex.conj_ofReal]
      ring
    · have h0 : h z = 0 := image_eq_zero_of_notMem_tsupport (fun hh => hz (hs hh))
      simp only [h0,zero_mul]
  refine ⟨?_,?_,?_⟩
  · rw [eL]
    exact hI1
  · rw [← eR]
    exact hJ2
  · rw [eL,he1,eM,he2,neg_neg,eR]

end TakhtajanTeo
