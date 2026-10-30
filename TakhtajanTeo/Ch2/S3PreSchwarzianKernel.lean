import TakhtajanTeo.Ch2.S1_LiouvilleWellDefined
import TakhtajanTeo.Ch2.S3KernelVariation

/-! # Actual pre-Schwarzian kernel inputs for Lemma 3.6

Finite energy is transported from the inverse Teichmüller class. In particular,
none of the area-integrability conclusions below are hypotheses.
-/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo.Ch2
open LiZhongQC

theorem s3pk_conj_disc {z : ℂ} : conj z ∈ unitDisc ↔ z ∈ unitDisc := by
  simp [unitDisc, mem_ball_zero_iff]

theorem s3pk_conj_exterior {z : ℂ} : conj z ∈ unitDiscExterior ↔ z ∈ unitDiscExterior := by
  simp [unitDiscExterior]

/-- Reflection in the real axis preserves the genuine holomorphic L2 space. -/
theorem s3pk_conj_A21 {D : Set ℂ} (hD : IsOpen D)
    (hconj : ∀ z, conj z ∈ D ↔ z ∈ D) {f : ℂ → ℂ} (hf : f ∈ A21fun D) :
    (fun z => conj (f (conj z))) ∈ A21fun D := by
  have hd : DifferentiableOn ℂ (fun z => conj (f (conj z))) D := by
    intro z hz
    have h := (hf.1.differentiableAt (hD.mem_nhds ((hconj z).mpr hz))).conj_conj
    simpa only [Complex.conj_conj, Function.comp_def] using! h.differentiableWithinAt
  have he : (fun z : ℂ => conj z) ⁻¹' D = D := Set.ext hconj
  have hm : MeasurePreserving (fun z : ℂ => conj z) (volume.restrict D) (volume.restrict D) := by
    have hm := Complex.conjLIE.measurePreserving.restrict_preimage hD.measurableSet
    change MeasurePreserving (fun z : ℂ => conj z)
      (volume.restrict ((fun z : ℂ => conj z) ⁻¹' D)) (volume.restrict D) at hm
    rwa [he] at hm
  have hl := (a21_memLp_two hD.measurableSet hf).comp_measurePreserving hm
  exact (mem_A21fun_iff_memLp hD.measurableSet).mpr ⟨hd,
    hl.congr_norm (hd.continuousOn.aestronglyMeasurable hD.measurableSet)
      (Eventually.of_forall fun z => by simp)⟩

/-- The actual inverse-class disk map, with its value at zero included. -/
theorem s3pk_gTilde_pair {ν : LinfStar} (hν : ν ∈ LinfStarBall) :
    EqOn (fun z => conj (fsans (beltramiInv ν) (conj z)))
      (fun z => derivAtInfty (gsans ν) * gTilde ν z) unitDisc := by
  intro z hz
  dsimp only
  by_cases hz0 : z = 0
  · subst z
    simp [gTilde, (s2c_facts (bc_beltramiInv_mem_ball hν)).2.2.1]
  · rw [(w3_eq_1_3 hν).1 (conj z) (s3pk_conj_disc.mpr hz) (by simpa using hz0)]
    simp [gTilde, hz0, refl, map_mul, map_inv₀, one_div]

theorem s3pk_fTilde_pair {ν : LinfStar} (hν : ν ∈ LinfStarBall) :
    EqOn (fun z => conj (gsans (beltramiInv ν) (conj z)))
      (fun z => derivAtInfty (gsans ν) * fTilde ν z) unitDiscExterior := by
  intro z hz
  dsimp only
  rw [(w3_eq_1_3 hν).2 (conj z) (s3pk_conj_exterior.mpr hz)]
  simp [fTilde, refl, map_mul, map_inv₀, one_div]

theorem s3pk_pre_gTilde {ν : LinfStar} (hν : ν ∈ LinfStarBall) :
    EqOn (preSchwarzian (gTilde ν))
      (fun z => conj (preSchwarzian (fsans (beltramiInv ν)) (conj z))) unitDisc := by
  obtain ⟨b,hb,hbg,-⟩ := s2c_gTilde_facts hν
  intro z hz
  have h := s2c_pre_congr (s3pk_gTilde_pair hν) isOpen_ball hz
  rw [s2c_conj_pre, s2c_pre_const_mul (hbg.symm ▸ hb)] at h
  exact h.symm

theorem s3pk_pre_fTilde {ν : LinfStar} (hν : ν ∈ LinfStarBall) :
    EqOn (preSchwarzian (fTilde ν))
      (fun z => conj (preSchwarzian (gsans (beltramiInv ν)) (conj z))) unitDiscExterior := by
  obtain ⟨b,hb,hbg,-⟩ := s2c_gTilde_facts hν
  intro z hz
  have h := s2c_pre_congr (s3pk_fTilde_pair hν) wp_exterior_isOpen hz
  rw [s2c_conj_pre, s2c_pre_const_mul (hbg.symm ▸ hb)] at h
  exact h.symm

/-- Finite energy for every actual representative of a point in T01. -/
theorem s3pk_representative_A21 {ν : LinfStar} (hν : ν ∈ LinfStarBall)
    (hp : Phi ⟨ν,hν⟩ ∈ T01) :
    preSchwarzian (fsans ν) ∈ A21fun unitDisc ∧
      preSchwarzian (gsans ν) ∈ A21fun unitDiscExterior := by
  have hrel : teichSetoid (Quotient.out (Phi ⟨ν,hν⟩)) ⟨ν,hν⟩ :=
    Quotient.exact (Quotient.out_eq (Phi ⟨ν,hν⟩))
  have he := s2c_class_pair hrel
  exact ⟨(ab112_A21fun_congr isOpen_ball (ab112_P_eqOn isOpen_ball he.1)).mp
      (ls1wd_preSchwarzian_disc hp),
    (ab112_A21fun_congr wp_exterior_isOpen (ab112_P_eqOn wp_exterior_isOpen he.2)).mp
      (ls1wd_preSchwarzian_exterior hp)⟩

theorem s3pk_tilde_A21 {p : T1} (hp : p ∈ T01) :
    let ν : LinfStar := (Quotient.out p : LinfStarBall)
    preSchwarzian (gTilde ν) ∈ A21fun unitDisc ∧
      preSchwarzian (fTilde ν) ∈ A21fun unitDiscExterior := by
  dsimp only
  let ν : LinfStar := (Quotient.out p : LinfStarBall)
  have hν : ν ∈ LinfStarBall := (Quotient.out p : LinfStarBall).2
  have hi := bc_beltramiInv_mem_ball hν
  have hp' : Phi ⟨beltramiInv ν,hi⟩ ∈ T01 := by
    rw [← ab112_invT_eq p]
    exact grp_lemma_3_4.2.2 p hp
  have hA := s3pk_representative_A21 hi hp'
  exact ⟨(ab112_A21fun_congr isOpen_ball (s3pk_pre_gTilde hν)).mpr
      (s3pk_conj_A21 isOpen_ball (fun _ => s3pk_conj_disc) hA.1),
    (ab112_A21fun_congr wp_exterior_isOpen (s3pk_pre_fTilde hν)).mpr
      (s3pk_conj_A21 wp_exterior_isOpen (fun _ => s3pk_conj_exterior) hA.2)⟩

theorem s3pk_tilde_energy_integrable {p : T1} (hp : p ∈ T01) :
    let ν : LinfStar := (Quotient.out p : LinfStarBall)
    IntegrableOn (fun z => ‖preSchwarzian (gTilde ν) z‖^2) unitDisc ∧
      IntegrableOn (fun z => ‖preSchwarzian (fTilde ν) z‖^2) unitDiscExterior :=
  ⟨a21_integrable_sq measurableSet_ball (s3pk_tilde_A21 hp).1,
    a21_integrable_sq wp_exterior_isOpen.measurableSet (s3pk_tilde_A21 hp).2⟩

/-- Actual mixed row transport, with both derivatives transported on open sets. -/
theorem s3pk_K2_tilde {ν : LinfStar} (hν : ν ∈ LinfStarBall) {z w : ℂ}
    (hz : z ∈ unitDisc) (hw : w ∈ unitDiscExterior) :
    kerK2 (gTilde ν) (fTilde ν) z w =
      conj (kerK2 (fsans (beltramiInv ν)) (gsans (beltramiInv ν)) (conj z) (conj w)) := by
  obtain ⟨b,hb,hbg,hgd,-⟩ := s2c_gTilde_facts hν
  have hfd := (s2c_fTilde_univ hν).1
  have hG := s3pk_gTilde_pair hν
  have hF := s3pk_fTilde_pair hν
  have hdG : conj (deriv (fsans (beltramiInv ν)) (conj z)) = b * deriv (gTilde ν) z := by
    have hh := (hG.deriv isOpen_ball) hz
    rw [s2c_conj_deriv, ((hgd.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt.const_mul _).deriv,
      hbg] at hh
    exact hh
  have hdF : conj (deriv (gsans (beltramiInv ν)) (conj w)) = b * deriv (fTilde ν) w := by
    have hh := (hF.deriv wp_exterior_isOpen) hw
    rw [s2c_conj_deriv, ((hfd.differentiableAt (wp_exterior_isOpen.mem_nhds hw)).hasDerivAt.const_mul _).deriv,
      hbg] at hh
    exact hh
  have hvG : conj (fsans (beltramiInv ν) (conj z)) = b * gTilde ν z := by
    simpa only [hbg] using hG hz
  have hvF : conj (gsans (beltramiInv ν) (conj w)) = b * fTilde ν w := by
    simpa only [hbg] using hF hw
  simp only [kerK2, map_mul, map_div₀, map_one, map_sub, map_pow, Complex.conj_ofReal,
    hdG, hdF, hvG, hvF]
  rw [← mul_sub, mul_pow,
    show b * deriv (gTilde ν) z * (b * deriv (fTilde ν) w) =
      b^2 * (deriv (gTilde ν) z * deriv (fTilde ν) w) by ring,
    mul_div_mul_left _ _ (pow_ne_zero 2 hb)]

theorem s3pk_K2_tilde_A21 {ν : LinfStar} (hν : ν ∈ LinfStarBall) {z : ℂ}
    (hz : z ∈ unitDisc) : (fun w => kerK2 (gTilde ν) (fTilde ν) z w) ∈ A21fun unitDiscExterior := by
  apply (ab112_A21fun_congr wp_exterior_isOpen (fun w hw => s3pk_K2_tilde hν hz hw)).mpr
  exact s3pk_conj_A21 wp_exterior_isOpen (fun _ => s3pk_conj_exterior)
    (s3kv_K2_row_A21 (bc_beltramiInv_mem_ball hν) (s3pk_conj_disc.mpr hz))

theorem s3pk_K1_tilde_A21 {ν : LinfStar} (hν : ν ∈ LinfStarBall) {z : ℂ}
    (hz : z ∈ unitDisc) : (fun w => kerK1 (gTilde ν) z w) ∈ A21fun unitDisc := by
  obtain ⟨b,hb,hbg,hd,hi,-⟩ := s2c_gTilde_facts hν
  exact AppB.kerK1_row_mem_A21 ⟨hd,hi⟩ hz

theorem s3pk_A21_pair_integrable {D : Set ℂ} (hD : MeasurableSet D)
    {φ ψ : ℂ → ℂ} (hφ : φ ∈ A21fun D) (hψ : ψ ∈ A21fun D) :
    IntegrableOn (fun w => φ w * conj (ψ w)) D := by
  have hc : MemLp (fun w => conj (ψ w)) 2 (volume.restrict D) :=
    (a21_memLp_two hD hψ).congr_norm
      (Complex.continuous_conj.comp_aestronglyMeasurable (hψ.1.continuousOn.aestronglyMeasurable hD))
      (Eventually.of_forall fun w => by simp)
  exact (a21_memLp_two hD hφ).integrable_mul hc

theorem s3pk_kernel_pair_integrable {p : T1} (hp : p ∈ T01) {z : ℂ} (hz : z ∈ unitDisc) :
    let ν : LinfStar := (Quotient.out p : LinfStarBall)
    IntegrableOn (fun w => kerK2 (gTilde ν) (fTilde ν) z w * conj (preSchwarzian (fTilde ν) w))
      unitDiscExterior ∧
    IntegrableOn (fun w => kerK1 (gTilde ν) z w * conj (preSchwarzian (gTilde ν) w)) unitDisc := by
  dsimp only
  exact ⟨s3pk_A21_pair_integrable wp_exterior_isOpen.measurableSet
      (s3pk_K2_tilde_A21 (Quotient.out p : LinfStarBall).2 hz) (s3pk_tilde_A21 hp).2,
    s3pk_A21_pair_integrable measurableSet_ball
      (s3pk_K1_tilde_A21 (Quotient.out p : LinfStarBall).2 hz) (s3pk_tilde_A21 hp).1⟩

/-- The literal quotient differs from the removable kernel only on a null singleton. -/
theorem s3pk_raw_disk_ae (g ψ : ℂ → ℂ) (z : ℂ) :
    (fun w => (deriv g z * deriv g w / (g z-g w)^2 - 1/(z-w)^2) * conj (ψ w))
      =ᵐ[volume.restrict unitDisc] fun w => -(π : ℂ) * (kerK1 g z w * conj (ψ w)) := by
  filter_upwards [(volume.restrict unitDisc).ae_ne z] with w hw
  rw [kerK1_of_ne g hw.symm]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  <;> ring

theorem s3pk_raw_exterior (f g ψ : ℂ → ℂ) (z w : ℂ) :
    deriv g z * deriv f w / (g z-f w)^2 * conj (ψ w) =
      (π : ℂ) * (kerK2 g f z w * conj (ψ w)) := by
  rw [kerK2]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

/-- Both literal integrals of the original Lemma 3.6 are absolutely integrable. -/
theorem s3pk_lemma_3_6_integrable {p : T1} (hp : p ∈ T01) {z : ℂ} (hz : z ∈ unitDisc) :
    let ν : LinfStar := (Quotient.out p : LinfStarBall)
    let f := fTilde ν
    let g := gTilde ν
    IntegrableOn (fun w => deriv g z * deriv f w / (g z-f w)^2 * conj (preSchwarzian f w))
      unitDiscExterior ∧
    IntegrableOn (fun w => (deriv g z * deriv g w / (g z-g w)^2 - 1/(z-w)^2) *
      conj (preSchwarzian g w)) unitDisc := by
  dsimp only
  have hi := s3pk_kernel_pair_integrable hp hz
  constructor
  · simpa only [s3pk_raw_exterior] using! hi.1.const_mul (π : ℂ)
  · exact (hi.2.const_mul (-(π : ℂ))).congr (s3pk_raw_disk_ae _ _ z).symm

/-- Exact conversion of the original right side to the two genuine kernel operators. -/
theorem s3pk_lemma_3_6_rhs (f g : ℂ → ℂ) (z : ℂ) :
    1 / (π : ℂ) * (∫ w in unitDiscExterior,
      deriv g z * deriv f w / (g z-f w)^2 * conj (preSchwarzian f w)) +
      1 / (π : ℂ) * (∫ w in unitDisc,
        (deriv g z * deriv g w / (g z-g w)^2 - 1/(z-w)^2) * conj (preSchwarzian g w)) =
      (∫ w in unitDiscExterior, kerK2 g f z w * conj (preSchwarzian f w)) -
        ∫ w in unitDisc, kerK1 g z w * conj (preSchwarzian g w) := by
  simp_rw [s3pk_raw_exterior]
  rw [integral_congr_ae (s3pk_raw_disk_ae g (preSchwarzian g) z), integral_const_mul,
    integral_const_mul]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  <;> ring

/-- Pulling the inverted pre-Schwarzian back gives the corrected logarithmic derivative. -/
theorem s3pk_inverted_pre_pullback {f : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D)
    (hf : DifferentiableOn ℂ f D) (hf0 : ∀ w ∈ D, f w ≠ 0)
    (hf1 : ∀ w ∈ D, deriv f w ≠ 0) {z : ℂ} (hz : z ∈ D) (hz0 : z ≠ 0) :
    preSchwarzian (fun ζ => 1 / f (1 / ζ)) (1 / z) * (-1 / z^2) =
      preSchwarzian f z - 2 * (deriv f z / f z - 1 / z) := by
  have h := s2c_A_inv hD hf hf0 hf1 (inv_ne_zero hz0) (by simpa using hz)
  simp only [inv_inv] at h
  simp only [one_div]
  rw [h]
  field_simp
  <;> ring

/-- The disk component of the actual `u = v - 2w` in Remark 3.10. -/
theorem s3pk_remark_linear_disc {ν : LinfStar} (hν : ν ∈ LinfStarBall) {z : ℂ}
    (hz : z ∈ unitDisc) (hz0 : z ≠ 0) :
    preSchwarzian (fun ζ => 1 / fsans ν (1 / ζ)) (1 / z) * (-1 / z^2) =
      preSchwarzian (fsans ν) z - 2 * (deriv (fsans ν) z / fsans ν z - 1 / z) := by
  obtain ⟨hfd,-,-,-,-,-,-,-,hf0,hf1⟩ := s2c_facts hν
  exact s3pk_inverted_pre_pullback (isOpen_ball.sdiff isClosed_singleton)
    (hfd.mono Set.sdiff_subset) (fun w hw => hf0 w hw.1 hw.2)
    (fun w hw => hf1 w hw.1) ⟨hz,hz0⟩ hz0

/-- The exterior component, with the original signs of u2, v2 and w2. -/
theorem s3pk_remark_linear_exterior {ν : LinfStar} (hν : ν ∈ LinfStarBall) {z : ℂ}
    (hz : z ∈ unitDiscExterior) :
    -(preSchwarzian (fun ζ => 1 / gsans ν (1 / ζ)) (1 / z) * (-1 / z^2)) =
      -preSchwarzian (gsans ν) z - 2 * (-(deriv (gsans ν) z / gsans ν z - 1 / z)) := by
  obtain ⟨-,-,-,-,hgd,-,hg0,hg1,-,-⟩ := s2c_facts hν
  have hz0 : z ≠ 0 := by
    intro h
    have hh : (1 : ℝ) < 0 := by simpa [h,unitDiscExterior] using hz
    linarith
  rw [s3pk_inverted_pre_pullback wp_exterior_isOpen hgd hg0 hg1 hz hz0]
  ring

end TakhtajanTeo.Ch2
