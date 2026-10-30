import TakhtajanTeo.Ch1.S7CutoffApproximation

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- Young's inequality in the precise complex form used by compact Green. -/
theorem s7cc_square (a b : ℂ) :
    ‖a‖ ^ 2 ≤ 2 * ((a + 2 * b) * conj a).re + 4 * ‖b‖ ^ 2 := by
  simp [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  nlinarith [sq_nonneg (a.re + 2*b.re), sq_nonneg (a.im + 2*b.im)]

private theorem compact_square_integrable {f : ℂ → ℂ}
    (hc : Continuous f) (hs : HasCompactSupport f) :
    Integrable (fun z => ‖f z‖ ^ 2) := by
  have h1 : Continuous (fun z : ℂ => ‖f z‖ ^ 2) := hc.norm.pow 2
  have h2 : HasCompactSupport (fun z : ℂ => ‖f z‖ ^ 2) :=
    hs.comp_left (g := fun v : ℂ => ‖v‖ ^ 2) (by simp)
  exact h1.integrable_of_hasCompactSupport (μ := volume) h2

/-- The cutoff gradient and boundary-error square are integrable by real compact support. -/
theorem s7cc_energy_integrable {h : ℂ → ℂ}
    (hh : ContDiffOn ℝ (⊤ : ℕ∞) h unitDisc) (n : ℕ) :
    Integrable (fun z => ‖(s7dc_cutoff n z : ℂ) * dzbar h z‖ ^ 2) ∧
    Integrable (fun z => ‖h z * dzbar (fun w => (s7dc_cutoff n w : ℂ)) z‖ ^ 2) := by
  let c : ℂ → ℂ := fun z => (s7dc_cutoff n z : ℂ)
  let A : ℂ → ℂ := fun z => c z * dzbar h z
  let B : ℂ → ℂ := fun z => h z * dzbar c z
  let T : ℂ → ℂ := fun z => c z ^ 2 * h z
  let P : ℂ → ℂ := fun z => T z * conj (laplace0 h z) * (rho z : ℂ)
  let J : ℂ → ℂ := fun z => dzbar T z * conj (dzbar h z)
  have hc : ContDiff ℝ (⊤ : ℕ∞) c := Complex.ofRealCLM.contDiff.comp (s7dc_smooth n)
  have hs : tsupport c ⊆ unitDisc := by
    have he : tsupport c = tsupport (s7dc_cutoff n) := by
      unfold tsupport
      congr 1
      ext z
      simp [c]
    rw [he]
    exact (s7dc_compact n).2
  have hcs : HasCompactSupport c := by
    exact (s7dc_compact n).1.comp_left (g := Complex.ofReal) (by simp)
  have hd : ContDiffOn ℝ (⊤ : ℕ∞) (dzbar h) unitDisc :=
    wp_contDiffOn_dzbar hh isOpen_ball (by simp)
  have hAc : ContDiff ℝ (⊤ : ℕ∞) A := sp_contDiff_mul isOpen_ball hd hc hs
  have hAs : HasCompactSupport A := hcs.mul_right
  have hdc : ContDiff ℝ (⊤ : ℕ∞) (dzbar c) := s7ca_dzbar_smooth hc
  have hdcs : HasCompactSupport (dzbar c) :=
    hcs.mono' (subset_closure.trans (s7ca_dzbar_support c))
  have hdss : tsupport (dzbar c) ⊆ unitDisc := (s7ca_dzbar_support c).trans hs
  have hBc : ContDiff ℝ (⊤ : ℕ∞) B := by
    simpa only [mul_comm] using sp_contDiff_mul isOpen_ball hh hdc hdss
  have hBs : HasCompactSupport B := hdcs.mul_left
  have hAE : Integrable (fun z => ‖A z‖ ^ 2) :=
    compact_square_integrable hAc.continuous hAs
  have hBE : Integrable (fun z => ‖B z‖ ^ 2) :=
    compact_square_integrable hBc.continuous hBs
  exact ⟨hAE,hBE⟩

/-- A compact cutoff energy inequality; every integral is genuinely integrable. -/
theorem s7cc_data {h : ℂ → ℂ}
    (hh : ContDiffOn ℝ (⊤ : ℕ∞) h unitDisc) (n : ℕ) :
    let c : ℂ → ℂ := fun z => (s7dc_cutoff n z : ℂ)
    let A : ℂ → ℂ := fun z => c z * dzbar h z
    let B : ℂ → ℂ := fun z => h z * dzbar c z
    let P : ℂ → ℂ := fun z => c z ^ 2 * h z * conj (laplace0 h z) * (rho z : ℂ)
    Integrable (fun z => ‖A z‖ ^ 2) ∧ Integrable (fun z => ‖B z‖ ^ 2) ∧
      Integrable P ∧
      Integrable (fun z => dzbar (fun w => c w ^ 2 * h w) z * conj (dzbar h z)) ∧
      (∫ z, P z) = ∫ z, dzbar (fun w => c w ^ 2 * h w) z * conj (dzbar h z) := by
  dsimp only
  let c : ℂ → ℂ := fun z => (s7dc_cutoff n z : ℂ)
  let A : ℂ → ℂ := fun z => c z * dzbar h z
  let B : ℂ → ℂ := fun z => h z * dzbar c z
  let T : ℂ → ℂ := fun z => c z ^ 2 * h z
  let P : ℂ → ℂ := fun z => T z * conj (laplace0 h z) * (rho z : ℂ)
  let J : ℂ → ℂ := fun z => dzbar T z * conj (dzbar h z)
  have hc : ContDiff ℝ (⊤ : ℕ∞) c := Complex.ofRealCLM.contDiff.comp (s7dc_smooth n)
  have hs : tsupport c ⊆ unitDisc := by
    have he : tsupport c = tsupport (s7dc_cutoff n) := by
      unfold tsupport
      congr 1
      ext z
      simp [c]
    rw [he]
    exact (s7dc_compact n).2
  have hcs : HasCompactSupport c := by
    exact (s7dc_compact n).1.comp_left (g := Complex.ofReal) (by simp)
  obtain ⟨hAE,hBE⟩ := s7cc_energy_integrable hh n
  change Integrable (fun z => ‖A z‖ ^ 2) at hAE
  change Integrable (fun z => ‖B z‖ ^ 2) at hBE
  have hc2 : ContDiff ℝ (⊤ : ℕ∞) (fun z => c z ^ 2) := hc.pow 2
  have hc2s : HasCompactSupport (fun z => c z ^ 2) :=
    hcs.comp_left (g := fun v : ℂ => v ^ 2) (by simp)
  have hc2ss : tsupport (fun z => c z ^ 2) ⊆ unitDisc := by
    simpa only [pow_two] using (tsupport_mul_subset_left (f := c) (g := c)).trans hs
  have hTc : ContDiff ℝ (⊤ : ℕ∞) T := sp_contDiff_mul isOpen_ball hh hc2 hc2ss
  have hTs : HasCompactSupport T := hc2s.mul_right
  have hTss : tsupport T ⊆ unitDisc := tsupport_mul_subset_left.trans hc2ss
  obtain ⟨hP, hJ, hG⟩ := s7cg_green (Or.inl rfl) (hh.of_le (by simp))
    (hTc.of_le (by simp)) hTs hTss
  change Integrable P at hP
  change Integrable J at hJ
  change (∫ z, P z) = ∫ z, J z at hG
  exact ⟨hAE,hBE,hP,hJ,hG⟩

/-- Pointwise energy comparison for the actual compact test. -/
theorem s7cc_pointwise {h : ℂ → ℂ}
    (hh : ContDiffOn ℝ (⊤ : ℕ∞) h unitDisc) (n : ℕ) (z : ℂ) :
    let c : ℂ → ℂ := fun z => (s7dc_cutoff n z : ℂ)
    ‖c z * dzbar h z‖ ^ 2 ≤
      2 * (dzbar (fun w => c w ^ 2 * h w) z * conj (dzbar h z)).re +
      4 * ‖h z * dzbar c z‖ ^ 2 := by
  dsimp only
  let c : ℂ → ℂ := fun z => (s7dc_cutoff n z : ℂ)
  let A : ℂ → ℂ := fun z => c z * dzbar h z
  let B : ℂ → ℂ := fun z => h z * dzbar c z
  let T : ℂ → ℂ := fun z => c z ^ 2 * h z
  let P : ℂ → ℂ := fun z => T z * conj (laplace0 h z) * (rho z : ℂ)
  let J : ℂ → ℂ := fun z => dzbar T z * conj (dzbar h z)
  have hc : ContDiff ℝ (⊤ : ℕ∞) c := Complex.ofRealCLM.contDiff.comp (s7dc_smooth n)
  have hs : tsupport c ⊆ unitDisc := by
    have he : tsupport c = tsupport (s7dc_cutoff n) := by
      unfold tsupport
      congr 1
      ext z
      simp [c]
    rw [he]
    exact (s7dc_compact n).2
  have hc2 : ContDiff ℝ (⊤ : ℕ∞) (fun z => c z ^ 2) := hc.pow 2
  have hdss : tsupport (dzbar c) ⊆ unitDisc := (s7ca_dzbar_support c).trans hs
  have hTss : tsupport T ⊆ unitDisc := by
    have ht : tsupport T ⊆ tsupport (fun z => c z ^ 2) := tsupport_mul_subset_left
    have ht2 : tsupport (fun z => c z ^ 2) ⊆ tsupport c := by
      simpa only [pow_two] using (tsupport_mul_subset_left (f := c) (g := c))
    exact ht.trans (ht2.trans hs)
  have hpoint (z : ℂ) : ‖A z‖ ^ 2 ≤ 2 * (J z).re + 4 * ‖B z‖ ^ 2 := by
    by_cases hz : z ∈ unitDisc
    · have hhz : DifferentiableAt ℝ h z :=
        (hh.differentiableOn (by simp) z hz).differentiableAt (isOpen_ball.mem_nhds hz)
      have hcz := hc.differentiable (by simp) z
      have ht : dzbar T z = c z ^ 2 * dzbar h z + 2 * c z * h z * dzbar c z := by
        dsimp [T]
        rw [s71_dzbar_mul (hc2.differentiable (by simp) z) hhz]
        have hcprod : dzbar (fun w => c w ^ 2) z = 2 * c z * dzbar c z := by
          simpa only [pow_two, two_mul, add_mul] using s71_dzbar_mul hcz hcz
        rw [hcprod]
        ring
      have hj : J z = (A z + 2 * B z) * conj (A z) := by
        dsimp [J, A, B]
        rw [ht, map_mul]
        have hreal : conj (c z) = c z := Complex.conj_ofReal _
        rw [hreal]
        ring
      rw [hj]
      exact s7cc_square _ _
    · have hc0 : c z = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hz (hs ht))
      have hd0 : dzbar c z = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hz (hdss ht))
      have hdt0 : dzbar T z = 0 := image_eq_zero_of_notMem_tsupport
        (fun ht => hz (hTss (s7ca_dzbar_support T ht)))
      simp [A, B, J, hc0, hd0, hdt0]
  exact hpoint z

/-- A compact cutoff energy inequality; every integral is genuinely integrable. -/
theorem s7cc_compact_estimate {h : ℂ → ℂ}
    (hh : ContDiffOn ℝ (⊤ : ℕ∞) h unitDisc) (n : ℕ) :
    let c : ℂ → ℂ := fun z => (s7dc_cutoff n z : ℂ)
    let A : ℂ → ℂ := fun z => c z * dzbar h z
    let B : ℂ → ℂ := fun z => h z * dzbar c z
    let P : ℂ → ℂ := fun z => c z ^ 2 * h z * conj (laplace0 h z) * (rho z : ℂ)
    Integrable (fun z => ‖A z‖ ^ 2) ∧ Integrable (fun z => ‖B z‖ ^ 2) ∧
      Integrable P ∧
      (∫ z, ‖A z‖ ^ 2) ≤ 2 * ‖∫ z, P z‖ + 4 * (∫ z, ‖B z‖ ^ 2) := by
  dsimp only
  let c : ℂ → ℂ := fun z => (s7dc_cutoff n z : ℂ)
  let A : ℂ → ℂ := fun z => c z * dzbar h z
  let B : ℂ → ℂ := fun z => h z * dzbar c z
  let T : ℂ → ℂ := fun z => c z ^ 2 * h z
  let P : ℂ → ℂ := fun z => T z * conj (laplace0 h z) * (rho z : ℂ)
  let J : ℂ → ℂ := fun z => dzbar T z * conj (dzbar h z)
  obtain ⟨hAE,hBE,hP,hJ,hG⟩ := s7cc_data hh n
  change Integrable (fun z => ‖A z‖ ^ 2) at hAE
  change Integrable (fun z => ‖B z‖ ^ 2) at hBE
  change Integrable P at hP
  change Integrable J at hJ
  change (∫ z, P z) = ∫ z, J z at hG
  have hpoint (z : ℂ) : ‖A z‖ ^ 2 ≤ 2 * (J z).re + 4 * ‖B z‖ ^ 2 :=
    s7cc_pointwise hh n z
  have hineq := integral_mono hAE ((hJ.re.const_mul 2).add (hBE.const_mul 4)) hpoint
  simp only [Pi.add_apply] at hineq
  rw [integral_add (hJ.re.const_mul 2) (hBE.const_mul 4), integral_const_mul,
    integral_const_mul, integral_re hJ, ← hG] at hineq
  refine ⟨hAE, hBE, hP, hineq.trans ?_⟩
  gcongr
  exact Complex.re_le_norm _

end TakhtajanTeo
