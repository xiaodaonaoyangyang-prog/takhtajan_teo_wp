import TakhtajanTeo.Ch2.S3Remark310
import TakhtajanTeo.Ch2.S4GFirstVariation

/-! # `S̃₁ = S₁` on `T₀(1)` (Program G, 下属4, prefix `s35_`)

`liouvilleS1Tilde_eq` writes `S̃₁ = ‖u‖² - 4π log|𝗀'(∞)|` for the same pair `(𝖿, 𝗀)` as `S₁ = ‖v‖² - 4π log|𝗀'(∞)|`.
By Remark 3.10 `u = -𝐊v̄`; in the Bergman bases `𝐊v̄` has coefficients `𝐁 x` (`s35_Kv_disc`, `s35_Kv_ext`) with
`x` the conjugated coefficients of `v`, and `𝐁*𝐁 = 𝐈` (`gop_blocks`) gives `‖u‖ = ‖v‖` (`s35_unitary`).
Consequences: the first two clauses of Theorem 3.8 are equivalent (`s35_thm38_clauses`), and Theorem 3.5 is
equivalent to the derivative clause of Theorem 3.8 (`s35_bers_transfer`).
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo.Ch2

open LiZhongQC

/-- Pointwise convergence of an `ℓ²` series in the Bergman basis of `𝔻*`. -/
theorem s35_seriesF_hasSum {x : ℕ → ℂ} (hx : Summable (fun n => ‖x n‖ ^ 2)) {u : ℂ}
    (hu : u ∈ unitDiscExterior) : HasSum (fun n => x n * basisF n u) (∑' n, x n * basisF n u) :=
  (bergman_pair_summable hx (e24_sq_of_abs (e24_absF hu))).of_norm.hasSum

/-- Parseval in the Bergman basis of `𝔻*`. -/
theorem s35_ext_parseval {x : ℕ → ℂ} (hx : Summable (fun n => ‖x n‖ ^ 2)) :
    HasSum (fun n => ‖x n‖ ^ 2) (∫ z in unitDiscExterior, ‖∑' n, x n * basisF n z‖ ^ 2) := by
  have h := e24_ext_pair hx hx (E := ∅) Set.finite_empty (fun u hu _ => s35_seriesF_hasSum hx hu)
    (fun u hu _ => s35_seriesF_hasSum hx hu)
  have e : ∀ w : ℂ, w * conj w = ((‖w‖ ^ 2 : ℝ) : ℂ) := fun w => by
    rw [Complex.mul_conj, Complex.sq_norm]
  simp only [e] at h
  rw [integral_complex_ofReal] at h
  exact Complex.hasSum_ofReal.mp h

/-- Every element of `A₂¹(𝔻*)` has an `ℓ²` expansion in the Bergman basis `f_n`, with Parseval. -/
theorem s35_ext_expansion {F : ℂ → ℂ} (hF : F ∈ A21fun unitDiscExterior) :
    ∃ x : ℕ → ℂ, Summable (fun n => ‖x n‖ ^ 2) ∧
      (∀ z ∈ unitDiscExterior, HasSum (fun n => x n * basisF n z) (F z)) ∧
      HasSum (fun n => ‖x n‖ ^ 2) (∫ z in unitDiscExterior, ‖F z‖ ^ 2) := by
  have hU : IsOpen (unitDisc \ {(0 : ℂ)}) := isOpen_ball.sdiff isClosed_singleton
  obtain ⟨H, hH, hHeq, -⟩ := a21_remove_puncture (a21_pullback hU a21_inversion_conformal hF)
  obtain ⟨y, hy, hys, -⟩ := A21_exists_ell2_expansion hH
  have hx : Summable (fun n => ‖-y n‖ ^ 2) := by simpa only [norm_neg] using hy
  have hser : ∀ z ∈ unitDiscExterior, HasSum (fun n => -y n * basisF n z) (F z) := by
    intro z hz
    obtain ⟨hzD, hz0⟩ := a21_inv_exterior hz
    have hz0' : z⁻¹ ≠ 0 := hz0
    have hzz : z ≠ 0 := fun h => hz0' (by rw [h, inv_zero])
    have h1 := hys z⁻¹ hzD
    have h2 : H z⁻¹ = F z * -(z⁻¹ ^ 2)⁻¹ := by
      rw [hHeq ⟨hzD, hz0⟩]
      show F z⁻¹⁻¹ * deriv (fun v : ℂ => v⁻¹) z⁻¹ = _
      rw [inv_inv, deriv_inv]
    have h3 := h1.mul_left (-(z⁻¹) ^ 2)
    rw [h2] at h3
    have h4 : -z⁻¹ ^ 2 * (F z * -(z⁻¹ ^ 2)⁻¹) = F z := by
      field_simp
    rw [h4] at h3
    refine h3.congr_fun (fun n => ?_)
    have hb := e24_basisF_inv n (inv_ne_zero hzz)
    rw [inv_inv] at hb
    rw [hb]
    ring
  refine ⟨fun n => -y n, hx, hser, ?_⟩
  have hP := s35_ext_parseval hx
  have hae : (fun z => ‖∑' n, -y n * basisF n z‖ ^ 2) =ᵐ[volume.restrict unitDiscExterior]
      fun z => ‖F z‖ ^ 2 := by
    filter_upwards [ae_restrict_mem (isOpen_lt continuous_const continuous_norm).measurableSet] with z hz
    rw [(hser z hz).tsum_eq]
  rwa [integral_congr_ae hae] at hP

/-- **The norm identity** `‖𝐁 x‖ = ‖x‖` for the block Grunsky operator (`𝐁*𝐁 = 𝐈`, `gop_blocks`). -/
theorem s35_unitary {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    (hF : volume ((f '' unitDisc ∪ g '' unitDiscExterior)ᶜ) = 0) (α α' : ell2) :
    ‖gopOp (B1 (grunsky f g)) α + gopOp (B2 (grunsky f g)) α'‖ ^ 2 +
        ‖gopOp (B3 (grunsky f g)) α + gopOp (B4 (grunsky f g)) α'‖ ^ 2 = ‖α‖ ^ 2 + ‖α'‖ ^ 2 := by
  obtain ⟨-, -, -, h1, h2, h3, -⟩ := gop_blocks h hF
  set T1 := gopOp (B1 (grunsky f g))
  set T2 := gopOp (B2 (grunsky f g))
  set T3 := gopOp (B3 (grunsky f g))
  set T4 := gopOp (B4 (grunsky f g))
  have key : ∀ (A B : ell2 →L[ℂ] ell2) (x y : ell2),
      inner ℂ (A x) (B y) = inner ℂ x ((ContinuousLinearMap.adjoint A * B) y) := by
    intro A B x y
    rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.adjoint_inner_right]
  have e1 : inner ℂ α ((ContinuousLinearMap.adjoint T1 * T1) α) +
      inner ℂ α ((ContinuousLinearMap.adjoint T3 * T3) α) = inner ℂ α α := by
    rw [← inner_add_right, ← ContinuousLinearMap.add_apply, h1, ContinuousLinearMap.one_apply]
  have e2 : inner ℂ α' ((ContinuousLinearMap.adjoint T2 * T2) α') +
      inner ℂ α' ((ContinuousLinearMap.adjoint T4 * T4) α') = inner ℂ α' α' := by
    rw [← inner_add_right, ← ContinuousLinearMap.add_apply, h2, ContinuousLinearMap.one_apply]
  have e3 : inner ℂ α ((ContinuousLinearMap.adjoint T1 * T2) α') +
      inner ℂ α ((ContinuousLinearMap.adjoint T3 * T4) α') = 0 := by
    rw [← inner_add_right, ← ContinuousLinearMap.add_apply, h3, ContinuousLinearMap.zero_apply, inner_zero_right]
  have e4 : inner ℂ α' ((ContinuousLinearMap.adjoint T2 * T1) α) +
      inner ℂ α' ((ContinuousLinearMap.adjoint T4 * T3) α) = 0 := by
    rw [← key, ← key, ← inner_conj_symm (T2 α'), ← inner_conj_symm (T4 α'), key, key, ← map_add, e3, map_zero]
  have hs : inner ℂ (T1 α + T2 α') (T1 α + T2 α') + inner ℂ (T3 α + T4 α') (T3 α + T4 α') =
      inner ℂ α α + inner ℂ α' α' := by
    simp only [inner_add_left, inner_add_right, key]
    linear_combination e1 + e2 + e3 + e4
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K,
    inner_self_eq_norm_sq_to_K] at hs
  exact_mod_cast hs

/-- The `ℓ²` vector `(\overline{a_n})`. -/
theorem s35_conj_mem {a : ℕ → ℂ} (ha : Summable (fun n => ‖a n‖ ^ 2)) :
    Memℓp (fun n => conj (a n)) 2 :=
  gop_mem_of_summable (by simpa only [RCLike.norm_conj] using ha)

/-- **`𝐊 v̄` in coefficients (disc).** If `V₁ = Σ aₙ eₙ` on `𝔻` and `V₂ = Σ a'ₙ fₙ` on `𝔻*`, then
`K₁V̄₁ + K₂V̄₂ = Σ_p (B₁ā + B₂ā')_p e_p` on `𝔻`. -/
theorem s35_Kv_disc {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    (hF : volume ((f '' unitDisc ∪ g '' unitDiscExterior)ᶜ) = 0) {a a' : ℕ → ℂ} {V₁ V₂ : ℂ → ℂ}
    (ha : Summable (fun n => ‖a n‖ ^ 2)) (ha' : Summable (fun n => ‖a' n‖ ^ 2))
    (hva : ∀ w ∈ unitDisc, HasSum (fun n => a n * basisE n w) (V₁ w))
    (hva' : ∀ w ∈ unitDiscExterior, HasSum (fun n => a' n * basisF n w) (V₂ w)) {z : ℂ} (hz : z ∈ unitDisc) :
    HasSum (fun p => (gopOp (B1 (grunsky f g)) ⟨_, s35_conj_mem ha⟩ +
        gopOp (B2 (grunsky f g)) ⟨_, s35_conj_mem ha'⟩ : ell2) p * basisE p z)
      ((∫ w in unitDisc, kerK1 f z w * conj (V₁ w)) + ∫ w in unitDiscExterior, kerK2 f g z w * conj (V₂ w)) := by
  obtain ⟨hsy, hcol1, -, -⟩ := mg_unitary_core h hF (B1 := B1 (grunsky f g))
    (B2 := B2 (grunsky f g)) (B3 := B3 (grunsky f g)) (B4 := B4 (grunsky f g))
    (fun m n => rfl) (fun m n => rfl) (fun m n => rfl) (fun m n => rfl)
  have hcolA : ∀ m n : ℕ, (∑' k, (conj (B1 (grunsky f g) k m) * B1 (grunsky f g) k n +
      conj (B3 (grunsky f g) k m) * B3 (grunsky f g) k n)) = if m = n then 1 else 0 := hcol1
  have hv := e24_absE hz
  obtain ⟨hx1, hx3, hK1, hK2⟩ := s310_rows_disc h hF hz
  have hI1 := e24_int_pair hx1 ha (E := {z}) (measure_singleton z)
    (fun u hu hn => hK1 u hu (fun h0 => hn (by simp [h0]))) (fun u hu _ => hva u hu)
  have hI2 := e24_ext_pair hx3 ha' (E := ∅) Set.finite_empty (fun u hu _ => hK2 u hu) (fun u hu _ => hva' u hu)
  have hS1 := s310_swap (M := B1 (grunsky f g)) (fun p => (e24_col hcolA p).1) hv ha
  have hS3 := s310_swap (M := B3 (grunsky f g)) (fun p => (e24_col hcolA p).2) hv ha'
  rw [hI1.unique hS1.2, hI2.unique hS3.2]
  have hB := gop_grunsky_bounds h hF
  obtain ⟨r1, b1⟩ := hB (B1 (grunsky f g)) (Set.mem_insert _ _)
  obtain ⟨r2, b2⟩ := hB (B2 (grunsky f g)) (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  refine (hS1.1.hasSum.add hS3.1.hasSum).congr_fun (fun p => ?_)
  rw [show ((gopOp (B1 (grunsky f g)) ⟨_, s35_conj_mem ha⟩ + gopOp (B2 (grunsky f g)) ⟨_, s35_conj_mem ha'⟩ :
      ell2) : ℕ → ℂ) p = gopOp (B1 (grunsky f g)) ⟨_, s35_conj_mem ha⟩ p +
        gopOp (B2 (grunsky f g)) ⟨_, s35_conj_mem ha'⟩ p from rfl]
  rw [gop_apply r1 b1, gop_apply r2 b2]
  have e1 : (∑' n, B1 (grunsky f g) p n * (⟨_, s35_conj_mem ha⟩ : ell2) n) =
      ∑' n, B1 (grunsky f g) n p * conj (a n) := tsum_congr (fun n => by rw [(hsy p n).1])
  have e2 : (∑' n, B2 (grunsky f g) p n * (⟨_, s35_conj_mem ha'⟩ : ell2) n) =
      ∑' n, B3 (grunsky f g) n p * conj (a' n) := tsum_congr (fun n => by rw [(hsy n p).2.2])
  rw [e1, e2]
  ring

/-- **`𝐊 v̄` in coefficients (exterior).** `K₃V̄₁ + K₄V̄₂ = Σ_q (B₃ā + B₄ā')_q f_q` on `𝔻*`. -/
theorem s35_Kv_ext {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    (hF : volume ((f '' unitDisc ∪ g '' unitDiscExterior)ᶜ) = 0) {a a' : ℕ → ℂ} {V₁ V₂ : ℂ → ℂ}
    (ha : Summable (fun n => ‖a n‖ ^ 2)) (ha' : Summable (fun n => ‖a' n‖ ^ 2))
    (hva : ∀ w ∈ unitDisc, HasSum (fun n => a n * basisE n w) (V₁ w))
    (hva' : ∀ w ∈ unitDiscExterior, HasSum (fun n => a' n * basisF n w) (V₂ w)) {z : ℂ}
    (hz : z ∈ unitDiscExterior) :
    HasSum (fun q => (gopOp (B3 (grunsky f g)) ⟨_, s35_conj_mem ha⟩ +
        gopOp (B4 (grunsky f g)) ⟨_, s35_conj_mem ha'⟩ : ell2) q * basisF q z)
      ((∫ w in unitDisc, kerK3 f g z w * conj (V₁ w)) + ∫ w in unitDiscExterior, kerK4 g z w * conj (V₂ w)) := by
  obtain ⟨hsy, -, hcol2, -⟩ := mg_unitary_core h hF (B1 := B1 (grunsky f g))
    (B2 := B2 (grunsky f g)) (B3 := B3 (grunsky f g)) (B4 := B4 (grunsky f g))
    (fun m n => rfl) (fun m n => rfl) (fun m n => rfl) (fun m n => rfl)
  have hcolB : ∀ m n : ℕ, (∑' k, (conj (B2 (grunsky f g) k m) * B2 (grunsky f g) k n +
      conj (B4 (grunsky f g) k m) * B4 (grunsky f g) k n)) = if m = n then 1 else 0 := hcol2
  have hv := e24_absF hz
  obtain ⟨hx2, hx4, hK3, hK4⟩ := s310_rows_ext h hF hz
  have hI3 := e24_int_pair hx2 ha (E := ∅) measure_empty (fun u hu _ => hK3 u hu) (fun u hu _ => hva u hu)
  have hI4 := e24_ext_pair hx4 ha' (E := {z}) (Set.finite_singleton z)
    (fun u hu hn => hK4 u hu (fun h0 => hn (by simp [h0]))) (fun u hu _ => hva' u hu)
  have hS2 := s310_swap (M := B2 (grunsky f g)) (fun p => (e24_col hcolB p).1) hv ha
  have hS4 := s310_swap (M := B4 (grunsky f g)) (fun p => (e24_col hcolB p).2) hv ha'
  rw [hI3.unique hS2.2, hI4.unique hS4.2]
  have hB := gop_grunsky_bounds h hF
  obtain ⟨r3, b3⟩ := hB (B3 (grunsky f g))
    (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
  obtain ⟨r4, b4⟩ := hB (B4 (grunsky f g))
    (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)))
  refine (hS2.1.hasSum.add hS4.1.hasSum).congr_fun (fun p => ?_)
  rw [show ((gopOp (B3 (grunsky f g)) ⟨_, s35_conj_mem ha⟩ + gopOp (B4 (grunsky f g)) ⟨_, s35_conj_mem ha'⟩ :
      ell2) : ℕ → ℂ) p = gopOp (B3 (grunsky f g)) ⟨_, s35_conj_mem ha⟩ p +
        gopOp (B4 (grunsky f g)) ⟨_, s35_conj_mem ha'⟩ p from rfl]
  rw [gop_apply r3 b3, gop_apply r4 b4]
  have e3 : (∑' n, B3 (grunsky f g) p n * (⟨_, s35_conj_mem ha⟩ : ell2) n) =
      ∑' n, B2 (grunsky f g) n p * conj (a n) := tsum_congr (fun n => by rw [(hsy p n).2.2])
  have e4 : (∑' n, B4 (grunsky f g) p n * (⟨_, s35_conj_mem ha'⟩ : ell2) n) =
      ∑' n, B4 (grunsky f g) n p * conj (a' n) := tsum_congr (fun n => by rw [(hsy p n).2.1])
  rw [e3, e4]
  ring

/-- **`S̃₁ = S₁` on `T₀(1)`.** By Remark 3.10 `u = -𝐊v̄`, and `𝐊` acts on Bergman coefficients by the unitary block
matrix `𝐁` (`𝐁*𝐁 = 𝐈`), so `‖u‖ = ‖v‖`; the two functions share the term `-4π log|𝗀'(∞)|`
(`liouvilleS1Tilde_eq`, first formula). -/
theorem s35_S1Tilde_eq {p : T1} (hp : p ∈ T01) : liouvilleS1Tilde p = liouvilleS1 p := by
  have hR := s310_remark_3_10 hp
  have hT := (liouvilleS1Tilde_eq hp).1
  set μ : LinfStar := ((Quotient.out p : LinfStarBall) : LinfStar) with hμdef
  dsimp only at hR hT
  have hμ : μ ∈ LinfStarBall := (Quotient.out p).2
  have hμT : Phi ⟨μ, hμ⟩ ∈ T01 := by
    rw [show Phi ⟨μ, hμ⟩ = p from Quotient.out_eq p]
    exact hp
  obtain ⟨hpair, hF, -⟩ := remark_2_2 hμ
  obtain ⟨hvA, hvB⟩ := s3pk_representative_A21 hμ hμT
  have hEm : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  obtain ⟨a, ha, hsa, hPa⟩ := A21_exists_ell2_expansion hvA
  obtain ⟨x, hx, hsx, hPx⟩ := s35_ext_expansion hvB
  have ha' : Summable (fun n => ‖-x n‖ ^ 2) := by simpa only [norm_neg] using hx
  have hsa' : ∀ w ∈ unitDiscExterior, HasSum (fun n => -x n * basisF n w) (-preSchwarzian (gsans μ) w) :=
    fun w hw => (hsx w hw).neg.congr_fun (fun n => by ring)
  set c : ell2 := gopOp (B1 (grunsky (fsans μ) (gsans μ))) ⟨_, s35_conj_mem ha⟩ +
    gopOp (B2 (grunsky (fsans μ) (gsans μ))) ⟨_, s35_conj_mem ha'⟩ with hc
  set d : ell2 := gopOp (B3 (grunsky (fsans μ) (gsans μ))) ⟨_, s35_conj_mem ha⟩ +
    gopOp (B4 (grunsky (fsans μ) (gsans μ))) ⟨_, s35_conj_mem ha'⟩ with hd
  -- the `u`-norms in coefficients
  have hcD : ∀ z ∈ unitDisc, z ∉ ({0} : Set ℂ) → HasSum (fun p => c p * basisE p z)
      (-(preSchwarzian (fsans μ) z - 2 * deriv (fsans μ) z / fsans μ z + 2 / z)) := by
    intro z hz hz0
    have hz0' : z ≠ 0 := fun h0 => hz0 (by simp [h0])
    have h1 := s35_Kv_disc hpair hF ha ha' hsa hsa' hz
    obtain ⟨-, hK, -, hu⟩ := hR.1 z hz hz0'
    simp only [if_pos hz] at hK
    rw [hK, hu] at h1
    convert h1 using 1
    ring
  have hdE : ∀ z ∈ unitDiscExterior, z ∉ (∅ : Set ℂ) → HasSum (fun q => d q * basisF q z)
      (preSchwarzian (gsans μ) z - 2 * deriv (gsans μ) z / gsans μ z + 2 / z) := by
    intro z hz _
    have hzD : z ∉ unitDisc := by
      intro h0
      have h1 : (1 : ℝ) < ‖z‖ := hz
      have h2 : ‖z‖ < 1 := mem_ball_zero_iff.mp h0
      linarith
    have h1 := s35_Kv_ext hpair hF ha ha' hsa hsa' hz
    obtain ⟨-, hK, -, hu⟩ := hR.2 z hz
    simp only [if_neg hzD] at hK
    rw [hK, hu] at h1
    convert h1 using 1
    ring
  have hcs : Summable (fun n => ‖c n‖ ^ 2) := gop_l2_summable c
  have hds : Summable (fun n => ‖d n‖ ^ 2) := gop_l2_summable d
  obtain ⟨-, hcae⟩ := s310_ae_seriesE hcs (measure_singleton 0) hcD
  obtain ⟨-, hdae⟩ := s310_ae_seriesF hds measure_empty hdE
  have hPc := (bergman_ell2_series hcs).2
  have hPd := s35_ext_parseval hds
  have hIc : (∫ z in unitDisc, ‖preSchwarzian (fsans μ) z - 2 * deriv (fsans μ) z / fsans μ z + 2 / z‖ ^ 2) =
      ∑' n, ‖c n‖ ^ 2 := by
    rw [hPc.tsum_eq]
    refine integral_congr_ae ?_
    filter_upwards [hcae] with z hz
    rw [← hz, norm_neg]
  have hId : (∫ z in unitDiscExterior, ‖preSchwarzian (gsans μ) z - 2 * deriv (gsans μ) z / gsans μ z + 2 / z‖ ^ 2) =
      ∑' n, ‖d n‖ ^ 2 := by
    rw [hPd.tsum_eq]
    refine integral_congr_ae ?_
    filter_upwards [hdae] with z hz
    rw [← hz]
  -- unitarity
  have hU := s35_unitary hpair hF ⟨_, s35_conj_mem ha⟩ ⟨_, s35_conj_mem ha'⟩
  rw [← hc, ← hd, gop_norm_sq, gop_norm_sq, gop_norm_sq, gop_norm_sq] at hU
  have hα : (∑' n, ‖(⟨_, s35_conj_mem ha⟩ : ell2) n‖ ^ 2) = ∑' n, ‖a n‖ ^ 2 :=
    tsum_congr (fun n => by show ‖conj (a n)‖ ^ 2 = _; rw [RCLike.norm_conj])
  have hα' : (∑' n, ‖(⟨_, s35_conj_mem ha'⟩ : ell2) n‖ ^ 2) = ∑' n, ‖x n‖ ^ 2 :=
    tsum_congr (fun n => by show ‖conj (-x n)‖ ^ 2 = _; rw [RCLike.norm_conj, norm_neg])
  rw [hα, hα', hPa.tsum_eq, hPx.tsum_eq] at hU
  rw [hT, hIc, hId, hU]
  rfl

/-- Near `e = 0` the chart points `[(e μ) * ν]` lie in `T₀(1)`, so `S̃₁ = S₁` there. -/
theorem s35_S1Tilde_eventually {p : T1} (hp : p ∈ T01) {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) :
    ∀ᶠ e : ℂ in 𝓝 0,
      liouvilleS1Tilde (ptT (beltramiMul (e • toLinf μ) ((Quotient.out p : LinfStarBall) : LinfStar))) =
        liouvilleS1 (ptT (beltramiMul (e • toLinf μ) ((Quotient.out p : LinfStarBall) : LinfStar))) := by
  set ν : LinfStar := ((Quotient.out p : LinfStarBall) : LinfStar) with hνdef
  have hν : ν ∈ LinfStarBall := (Quotient.out p).2
  have hνT : Phi ⟨ν, hν⟩ ∈ T01 := by
    rw [show Phi ⟨ν, hν⟩ = p from Quotient.out_eq p]
    exact hp
  have h0 : normL2 unitDiscExterior ⇑(0 : LinfStar) = 0 := by
    unfold normL2
    rw [lintegral_congr_ae (g := fun _ => 0) ?_, lintegral_zero, ENNReal.zero_rpow_of_pos (by norm_num)]
    filter_upwards [Lp.coeFn_zero ℂ ∞ (volume.restrict unitDiscExterior)] with z hz
    rw [hz]
    simp
  have hsmall : ∀ᶠ e : ℂ in 𝓝 0, ‖e‖ * ‖toLinf μ‖ < 1 ∧ ‖e‖ ≤ 1 := by
    refine ((continuous_norm.mul continuous_const).continuousAt.eventually_lt continuousAt_const
      (by simp)).and ?_
    exact (continuous_norm.continuousAt.eventually_lt continuousAt_const (by simp)).mono fun e he => he.le
  filter_upwards [hsmall] with e he
  have hball : e • toLinf μ ∈ LinfStarBall := by
    rw [LinfStarBall, mem_ball_zero_iff, norm_smul]
    exact he.1
  have hL : normL2 unitDiscExterior ⇑(e • toLinf μ) < ∞ := by
    have h := s4g_normL2_line 0 hμ he.2
    rw [zero_add, h0, zero_add] at h
    exact h.trans_lt hμ.choose_spec.2.2
  have hmem := bg_mul_mem_ball hν hball
  have hT := s4g_T01_mul hν hνT hball hL
  rw [ptT, dif_pos hmem]
  exact s35_S1Tilde_eq hT

/-- `∂S̃₁ = ∂S₁` in the Bers coordinates of every chart centred in `T₀(1)`: Theorem 3.5 is equivalent to the
derivative clause of Theorem 3.8. -/
theorem s35_bers_transfer {p : T1} (hp : p ∈ T01) {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) :
    (BersDiffAt liouvilleS1Tilde (Quotient.out p : LinfStarBall) μ ↔
        BersDiffAt liouvilleS1 (Quotient.out p : LinfStarBall) μ) ∧
      bersDz liouvilleS1Tilde (Quotient.out p : LinfStarBall) μ =
        bersDz liouvilleS1 (Quotient.out p : LinfStarBall) μ := by
  have hev : (fun e : ℂ => liouvilleS1Tilde (ptT (beltramiMul (e • toLinf μ)
      ((Quotient.out p : LinfStarBall) : LinfStar)))) =ᶠ[𝓝 (0 : ℂ)] fun e : ℂ =>
      liouvilleS1 (ptT (beltramiMul (e • toLinf μ) ((Quotient.out p : LinfStarBall) : LinfStar))) :=
    s35_S1Tilde_eventually hp hμ
  refine ⟨?_, ?_⟩
  · unfold BersDiffAt
    exact hev.differentiableAt_iff
  · unfold bersDz
    refine l613_dz_congr ?_
    filter_upwards [hev] with e he
    simp only [he]

/-- Theorem 3.8, first two clauses: they are equivalent on `T₀(1)`. -/
theorem s35_thm38_clauses {F : T1 → ℝ} :
    (∀ p ∈ T01, F p = -(1 / (12 * π)) * liouvilleS1 p) ↔
      ∀ p ∈ T01, F p = -(1 / (12 * π)) * liouvilleS1Tilde p := by
  constructor
  · intro h p hp
    rw [s35_S1Tilde_eq hp]
    exact h p hp
  · intro h p hp
    rw [← s35_S1Tilde_eq hp]
    exact h p hp

end TakhtajanTeo.Ch2
