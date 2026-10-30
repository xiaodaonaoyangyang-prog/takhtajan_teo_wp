import TakhtajanTeo.Ch1.WeightedBergman

/-!
# Bergman reproducing formula on the upper half-plane for `A∞(𝕌)` (TT:1236–1242)

By the Cayley transform `u ↦ (u - i)/(u + i)` from the formula on `𝔻` (`WeightedBergman`):
`∬_𝕌 (Im u)² φ(u) (ū - z)⁻⁴ d²u = (π/12) φ(z)` for `φ` holomorphic on `𝕌` with `sup (Im u)² |φ| < ∞`.
This gives the two clauses of `harmonicProjU_spec` (relocated from `S1_5_Variational` to avoid an import cycle).
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

/-- The Cayley transform `𝕌 → 𝔻`, `u ↦ (u - i)/(u + i)`. -/
theorem hp_cay_ne {u : ℂ} (hu : u ∈ upperHalf) : u + I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  have hu' : 0 < u.im := hu
  simp at this
  linarith

theorem hp_cay_norm_sq {u : ℂ} (hu : u ∈ upperHalf) :
    1 - ‖(u - I) / (u + I)‖ ^ 2 = 4 * u.im / ‖u + I‖ ^ 2 := by
  have hne := hp_cay_ne hu
  have hn : ‖u + I‖ ≠ 0 := norm_ne_zero_iff.mpr hne
  rw [norm_div]
  field_simp
  have h1 : ‖u - I‖ ^ 2 = u.re ^ 2 + (u.im - 1) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  have h2 : ‖u + I‖ ^ 2 = u.re ^ 2 + (u.im + 1) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  rw [h1, h2]; ring

theorem hp_cay_mem {u : ℂ} (hu : u ∈ upperHalf) : (u - I) / (u + I) ∈ unitDisc := by
  have h := hp_cay_norm_sq hu
  have hu' : 0 < u.im := hu
  have hn : 0 < ‖u + I‖ := norm_pos_iff.mpr (hp_cay_ne hu)
  have : 0 < 1 - ‖(u - I) / (u + I)‖ ^ 2 := by rw [h]; positivity
  simp only [unitDisc, mem_ball, dist_zero_right]
  nlinarith [norm_nonneg ((u - I) / (u + I))]

/-- Inverse Cayley transform `s ↦ i (1 + s)/(1 - s)`. -/
theorem hp_icay_mem {s : ℂ} (hs : s ∈ unitDisc) : I * ((1 + s) / (1 - s)) ∈ upperHalf := by
  have hsn : ‖s‖ < 1 := by simpa [unitDisc] using hs
  have hne : 1 - s ≠ 0 := by
    intro h
    have : s = 1 := by linear_combination -h
    rw [this] at hsn; simp at hsn
  have hn : 0 < ‖1 - s‖ ^ 2 := by positivity
  have hnsq : ‖1 - s‖ ^ 2 = (1 - s.re) ^ 2 + s.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  have hs2 : ‖s‖ ^ 2 = s.re ^ 2 + s.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hq : (1 - s.re) ^ 2 + s.im ^ 2 ≠ 0 := by rw [← hnsq]; exact hn.ne'
  have key : ((1 + s) / (1 - s)).re = (1 - ‖s‖ ^ 2) / ‖1 - s‖ ^ 2 := by
    rw [Complex.div_re, Complex.normSq_apply, hnsq, hs2]
    simp only [Complex.add_re, Complex.one_re, Complex.sub_re, Complex.add_im, Complex.one_im, Complex.sub_im]
    have hd : (1 - s.re) * (1 - s.re) + (0 - s.im) * (0 - s.im) = (1 - s.re) ^ 2 + s.im ^ 2 := by ring
    rw [hd, ← add_div]
    congr 1
    ring
  show 0 < (I * ((1 + s) / (1 - s))).im
  rw [Complex.mul_im]; simp only [Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add]
  rw [key]
  apply div_pos
  · nlinarith [norm_nonneg s]
  · exact hn

theorem hp_icay_cay {u : ℂ} (hu : u ∈ upperHalf) :
    I * ((1 + (u - I) / (u + I)) / (1 - (u - I) / (u + I))) = u := by
  have hne := hp_cay_ne hu
  have h2 : (2 * I : ℂ) ≠ 0 := by simp
  field_simp
  ring_nf
  try simp [Complex.I_sq]
  try ring

theorem hp_cay_icay {s : ℂ} (hs : s ∈ unitDisc) :
    (I * ((1 + s) / (1 - s)) - I) / (I * ((1 + s) / (1 - s)) + I) = s := by
  have hsn : ‖s‖ < 1 := by simpa [unitDisc] using hs
  have hne : 1 - s ≠ 0 := by
    intro h
    have : s = 1 := by linear_combination -h
    rw [this] at hsn; simp at hsn
  have e1 : I * ((1 + s) / (1 - s)) - I = I * (2 * s) / (1 - s) := by field_simp; ring
  have e2 : I * ((1 + s) / (1 - s)) + I = I * 2 / (1 - s) := by field_simp; ring
  rw [e1, e2]
  have hI : (I : ℂ) * 2 ≠ 0 := by simp
  field_simp

theorem hp_cay_hasDerivAt {u : ℂ} (hu : u ∈ upperHalf) :
    HasDerivAt (fun x : ℂ => (x - I) / (x + I)) (2 * I / (u + I) ^ 2) u := by
  have hne := hp_cay_ne hu
  have h := ((hasDerivAt_id' u).sub_const I).div ((hasDerivAt_id' u).add_const I) hne
  refine h.congr_deriv ?_
  field_simp
  ring

theorem hp_cay_injOn : InjOn (fun x : ℂ => (x - I) / (x + I)) upperHalf := by
  intro a ha b hb h
  have := congrArg (fun s : ℂ => I * ((1 + s) / (1 - s))) h
  simp only at this
  rwa [hp_icay_cay ha, hp_icay_cay hb] at this

theorem hp_cay_image : (fun x : ℂ => (x - I) / (x + I)) '' upperHalf = unitDisc := by
  ext s
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact hp_cay_mem hu
  · intro hs
    exact ⟨_, hp_icay_mem hs, hp_cay_icay hs⟩

/-- `1 - cay u = 2i/(u + i)`. -/
theorem hp_one_sub_cay {u : ℂ} (hu : u ∈ upperHalf) : 1 - (u - I) / (u + I) = 2 * I / (u + I) := by
  have hne := hp_cay_ne hu
  field_simp
  ring

/-- `1 - cay z · conj (cay u) = 2i (ū - z)/((z + i)(ū - i))`. -/
theorem hp_kernel_cay {u z : ℂ} (hu : u ∈ upperHalf) (hz : z ∈ upperHalf) :
    1 - (z - I) / (z + I) * conj ((u - I) / (u + I)) = 2 * I * (conj u - z) / ((z + I) * (conj u - I)) := by
  have hz' := hp_cay_ne hz
  have hu' : conj u - I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    have hu0 : 0 < u.im := hu
    simp at this
    linarith
  have core : ∀ a z : ℂ, z + I ≠ 0 → a - I ≠ 0 →
      1 - (z - I) / (z + I) * ((a + I) / (a - I)) = 2 * I * (a - z) / ((z + I) * (a - I)) := by
    intro a z h1 h2
    field_simp
    ring_nf
    try simp [Complex.I_sq]
    try ring
  rw [map_div₀, map_sub, map_add, Complex.conj_I, show conj u - -I = conj u + I by ring,
    show conj u + -I = conj u - I by ring]
  exact core _ _ hz' hu'

theorem hp_pointwise {u z : ℂ} (hu : u ∈ upperHalf) (hz : z ∈ upperHalf) (φu : ℂ) :
    ‖(2 * I / (u + I) ^ 2 : ℂ)‖ ^ 2 • ((-(u + I) ^ 4 / 4 * φu) *
        ((((1 - ‖(u - I) / (u + I)‖ ^ 2) ^ 2 : ℝ)) : ℂ) / (1 - (z - I) / (z + I) * conj ((u - I) / (u + I))) ^ 4) =
      -(z + I) ^ 4 * ((((u.im) ^ 2 : ℝ) : ℂ) * φu / (conj u - z) ^ 4) := by
  have hne := hp_cay_ne hu
  have hz' := hp_cay_ne hz
  have hu' : conj u - I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    have hu0 : 0 < u.im := hu
    simp at this
    linarith
  have hzu : conj u - z ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    have hu0 : 0 < u.im := hu
    have hz0 : 0 < z.im := hz
    simp at this
    linarith
  have hN : ((‖u + I‖ : ℝ) : ℂ) ^ 2 = (u + I) * (conj u - I) := by
    rw [← Complex.mul_conj', map_add, Complex.conj_I]; ring
  have hnorm : ‖(2 * I / (u + I) ^ 2 : ℂ)‖ ^ 2 = 4 / ‖u + I‖ ^ 4 := by
    rw [norm_div, norm_pow]; simp; field_simp; ring
  have h1 := hp_cay_norm_sq hu
  have hnr : 0 < ‖u + I‖ := norm_pos_iff.mpr hne
  have hw : (((1 - ‖(u - I) / (u + I)‖ ^ 2) ^ 2 : ℝ) : ℂ) = 16 * (((u.im) ^ 2 : ℝ) : ℂ) / ((‖u + I‖ : ℝ) : ℂ) ^ 4 := by
    rw [h1]; push_cast; field_simp; ring
  rw [hp_kernel_cay hu hz, hw, hnorm, Complex.real_smul]
  have hN4 : ((‖u + I‖ : ℝ) : ℂ) ^ 4 = ((u + I) * (conj u - I)) ^ 2 := by
    rw [← hN]; ring
  push_cast
  rw [hN4]
  have h2 : (I : ℂ) ^ 4 = 1 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Complex.I_sq]; norm_num
  field_simp
  ring_nf
  simp [Complex.I_sq, h2]
  try ring

theorem hp_phit_cay {φ : ℂ → ℂ} {u : ℂ} (hu : u ∈ upperHalf) :
    φ (I * ((1 + (u - I) / (u + I)) / (1 - (u - I) / (u + I)))) * (2 * I / (1 - (u - I) / (u + I)) ^ 2) ^ 2 =
      -(u + I) ^ 4 / 4 * φ u := by
  have hne := hp_cay_ne hu
  rw [hp_icay_cay hu, hp_one_sub_cay hu]
  have h2 : (2 * I : ℂ) ≠ 0 := by simp
  field_simp
  ring_nf
  simp [Complex.I_sq]
  try ring

/-- The Bergman reproducing formula on the upper half-plane for `A∞(𝕌)`. -/
theorem hp_bergman {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ upperHalf) {C : ℝ}
    (hC : ∀ u ∈ upperHalf, ‖φ u‖ * u.im ^ 2 ≤ C) {z : ℂ} (hz : z ∈ upperHalf) :
    ∫ u in upperHalf, (((u.im) ^ 2 : ℝ) : ℂ) * φ u / (conj u - z) ^ 4 = ((π / 12 : ℝ) : ℂ) * φ z := by
  have hopen : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  set φt : ℂ → ℂ := fun s => φ (I * ((1 + s) / (1 - s))) * (2 * I / (1 - s) ^ 2) ^ 2 with hφt
  have hne1 : ∀ s ∈ unitDisc, 1 - s ≠ 0 := by
    intro s hs h
    have hsn : ‖s‖ < 1 := by simpa [unitDisc] using hs
    have : s = 1 := by linear_combination -h
    rw [this] at hsn; simp at hsn
  have hdiff : DifferentiableOn ℂ φt unitDisc := by
    intro s hs
    have hs1 := hne1 s hs
    have hic : DifferentiableAt ℂ (fun s : ℂ => I * ((1 + s) / (1 - s))) s :=
      (differentiableAt_const _).mul (((differentiableAt_const _).add differentiableAt_id).div
        ((differentiableAt_const _).sub differentiableAt_id) hs1)
    have hφat : DifferentiableAt ℂ φ (I * ((1 + s) / (1 - s))) :=
      hφ.differentiableAt (hopen.mem_nhds (hp_icay_mem hs))
    have h2 : DifferentiableAt ℂ (fun s : ℂ => (2 * I / (1 - s) ^ 2) ^ 2) s := by
      have hd : DifferentiableAt ℂ (fun s : ℂ => (1 - s) ^ 2) s :=
        ((differentiableAt_const _).sub differentiableAt_id).pow 2
      exact ((differentiableAt_const _).div hd (pow_ne_zero _ hs1)).pow 2
    exact ((hφat.comp s hic).mul h2).differentiableWithinAt
  have hbound : ∀ s ∈ unitDisc, ‖φt s‖ * (1 - ‖s‖ ^ 2) ^ 2 ≤ 4 * C := by
    intro s hs
    obtain ⟨u, hu, rfl⟩ : ∃ u ∈ upperHalf, (u - I) / (u + I) = s := by
      exact ⟨_, hp_icay_mem hs, hp_cay_icay hs⟩
    have hne := hp_cay_ne hu
    have hnr : 0 < ‖u + I‖ := norm_pos_iff.mpr hne
    rw [hφt]; simp only
    rw [hp_phit_cay hu, hp_cay_norm_sq hu, norm_mul, norm_div, norm_neg, norm_pow]
    simp only [norm_ofNat]
    have := hC u hu
    have hy : 0 < u.im := hu
    have e : ‖u + I‖ ^ 4 / 4 * ‖φ u‖ * (4 * u.im / ‖u + I‖ ^ 2) ^ 2 = 4 * (‖φ u‖ * u.im ^ 2) := by
      field_simp
    rw [e]; linarith
  have hw : (z - I) / (z + I) ∈ unitDisc := hp_cay_mem hz
  have hrep := wb_Ainf_reproducing hdiff hbound hw
  have hint := ahP_integral_image (f := fun x : ℂ => (x - I) / (x + I)) hopen
    (fun u hu => (hp_cay_hasDerivAt hu).differentiableAt.differentiableWithinAt) hp_cay_injOn
    (fun s => φt s * (((1 - ‖s‖ ^ 2 : ℝ) ^ 2 : ℝ) : ℂ) / (1 - (z - I) / (z + I) * conj s) ^ 4)
  rw [hp_cay_image] at hint
  have hpt : ∀ u ∈ upperHalf, ‖deriv (fun x : ℂ => (x - I) / (x + I)) u‖ ^ 2 •
      (φt ((u - I) / (u + I)) * (((1 - ‖(u - I) / (u + I)‖ ^ 2 : ℝ) ^ 2 : ℝ) : ℂ) /
        (1 - (z - I) / (z + I) * conj ((u - I) / (u + I))) ^ 4) =
      -(z + I) ^ 4 * ((((u.im) ^ 2 : ℝ) : ℂ) * φ u / (conj u - z) ^ 4) := by
    intro u hu
    rw [(hp_cay_hasDerivAt hu).deriv, hφt]
    simp only
    rw [hp_phit_cay hu]
    exact hp_pointwise hu hz (φ u)
  rw [setIntegral_congr_fun hopen.measurableSet hpt, integral_const_mul] at hint
  rw [hφt] at hrep
  simp only at hrep
  rw [hp_phit_cay hz, hint] at hrep
  have hz' := hp_cay_ne hz
  have h4 : (z + I) ^ 4 ≠ 0 := pow_ne_zero _ hz'
  have hπ : ((π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  set J := ∫ u in upperHalf, (((u.im) ^ 2 : ℝ) : ℂ) * φ u / (conj u - z) ^ 4 with hJ
  push_cast at hrep ⊢
  have hπ' : (π : ℂ) * (3 / π) = 3 := by field_simp
  refine mul_left_cancel₀ h4 ?_
  linear_combination ((π : ℂ) / 3) * hrep - ((z + I) ^ 4 * J / 3) * hπ'

/-- The key integral for `μ = ((u - ū)²/2) φ̄`: `∬_𝕌 \overline{μ(u)} (ū - z)⁻⁴ d²u = -(π/6) φ(z)`. -/
theorem hp_harmonic_integral {μ φ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) {z : ℂ} (hz : z ∈ upperHalf) :
    ∫ u in upperHalf, conj (μ u) / (conj u - z) ^ 4 = -((π / 6 : ℝ) : ℂ) * φ z := by
  obtain ⟨hφd, ⟨C, hC⟩, hμrep⟩ := hμ
  have hopen : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hC' : ∀ u ∈ upperHalf, ‖φ u‖ * u.im ^ 2 ≤ C := by
    intro u hu
    have h := hC u hu
    have e : ‖(u.im : ℂ) ^ 2 * φ u‖ = ‖φ u‖ * u.im ^ 2 := by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]; ring
    rw [e] at h; exact h
  have hcm : ∀ u ∈ upperHalf, conj (μ u) = -2 * (((u.im) ^ 2 : ℝ) : ℂ) * φ u := by
    intro u hu
    rw [hμrep u hu]
    simp only [map_mul, map_div₀, map_pow, map_sub, Complex.conj_conj]
    have : (u - conj u) = 2 * I * (u.im : ℂ) := by
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
    have h2 : (conj u - u) = -(2 * I * (u.im : ℂ)) := by rw [← neg_sub, this]
    rw [h2]
    simp only [map_ofNat]
    push_cast
    ring_nf
    simp [Complex.I_sq]
  have := hp_bergman hφd hC' hz
  rw [setIntegral_congr_fun hopen.measurableSet (fun u hu => by rw [hcm u hu])]
  have e2 : ∀ u ∈ upperHalf, -2 * (((u.im) ^ 2 : ℝ) : ℂ) * φ u / (conj u - z) ^ 4 =
      -2 * ((((u.im) ^ 2 : ℝ) : ℂ) * φ u / (conj u - z) ^ 4) := fun u _ => by ring
  rw [setIntegral_congr_fun hopen.measurableSet e2, integral_const_mul, this]
  push_cast
  ring

/-- (TT:1236–1242) `P` of (1.23) fixes `Ω^{-1,1}(𝕌)`, and for `μ = ((z - z̄)²/2) φ̄` with `φ ∈ A∞(𝕌)`,
`Φ[μ]_{zzz} = φ` on `𝕌`. -/
theorem harmonicProjU_spec {μ φ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) :
    (∀ z ∈ upperHalf, harmonicProjU μ z = μ z) ∧ ∀ z ∈ upperHalf, iteratedDeriv 3 (varPhi μ) z = φ z := by
  have hopen : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hint : ∀ z ∈ upperHalf, ∫ u in upperHalf, conj (μ u) / (conj u - z) ^ 4 = -((π / 6 : ℝ) : ℂ) * φ z :=
    fun z hz => hp_harmonic_integral hμ hz
  obtain ⟨hφd, ⟨C, hC⟩, hμrep⟩ := hμ
  have hC' : ∀ u ∈ upperHalf, ‖φ u‖ * u.im ^ 2 ≤ C := by
    intro u hu
    have h := hC u hu
    have e : ‖(u.im : ℂ) ^ 2 * φ u‖ = ‖φ u‖ * u.im ^ 2 := by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]; ring
    rw [e] at h; exact h
  have hC0 : 0 ≤ C := by
    have hI : (I : ℂ) ∈ upperHalf := by simp [upperHalf]
    have := hC' I hI
    simp at this
    exact (norm_nonneg _).trans this
  have hnorm : ∀ u ∈ upperHalf, ‖μ u‖ = 2 * (‖φ u‖ * u.im ^ 2) := by
    intro u hu
    have h1 : (u - conj u) = 2 * I * (u.im : ℂ) := by
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
    rw [hμrep u hu, norm_mul, norm_div, norm_pow, h1, Complex.norm_conj]
    simp
    rw [mul_pow, sq_abs]
    ring
  have hμb : IsBeltramiCoeff μ upperHalf (2 * C) := by
    refine ⟨?_, ?_⟩
    · have hc : ContinuousOn (fun u => (u - conj u) ^ 2 / 2 * conj (φ u)) upperHalf :=
        ((continuous_id.sub Complex.continuous_conj).pow 2 |>.div_const 2).continuousOn.mul
          (Complex.continuous_conj.comp_continuousOn hφd.continuousOn)
      refine (hc.aestronglyMeasurable hopen.measurableSet).congr ?_
      filter_upwards [ae_restrict_mem hopen.measurableSet] with u hu
      exact (hμrep u hu).symm
    · filter_upwards [ae_restrict_mem hopen.measurableSet] with u hu
      rw [hnorm u hu]
      linarith [hC' u hu]
  have hvar := (varPhi_holomorphic_of_bounded (by linarith) hμb).2
  have hπ : ((π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · have hconj : ∫ u in upperHalf, μ u / (u - conj z) ^ 4 = -((π / 6 : ℝ) : ℂ) * conj (φ z) := by
      have h := congrArg conj (hint z hz)
      rw [← integral_conj] at h
      have e : ∀ u : ℂ, conj (conj (μ u) / (conj u - z) ^ 4) = μ u / (u - conj z) ^ 4 := by
        intro u
        simp only [map_div₀, map_pow, map_sub, Complex.conj_conj]
      simp only [e] at h
      rw [h]
      simp only [map_mul, map_neg, Complex.conj_ofReal]
    unfold harmonicProjU
    rw [hconj, hμrep z hz]
    push_cast
    field_simp
    ring
  · rw [hvar z hz, hint z hz]
    push_cast
    field_simp

end TakhtajanTeo
