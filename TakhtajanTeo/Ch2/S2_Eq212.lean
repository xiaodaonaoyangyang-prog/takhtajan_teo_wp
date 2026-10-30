import TakhtajanTeo.Ch2.S2_Completed6
import TakhtajanTeo.Ch2.S2_Completed3
import TakhtajanTeo.Ch2.S2_MixedHook
import TakhtajanTeo.Ch2.S2_Cor29
import TakhtajanTeo.Ch2.S2_Remark22
import TakhtajanTeo.Ch1.S2Core
import TakhtajanTeo.Ch2.FaberGramIntegral
import TakhtajanTeo.Ch2.S1_T112Completed
import LiZhongQC.RiemannMapping
import TakhtajanTeo.Ch2.S2_GrunskyOp
import TakhtajanTeo.Ch2.S2_Remark23

/-!
# Ch2 §2: (2.12), Fredholm eigenvalues and the singular values of `B₁` (`e212_`, 下属2)

Host: new module `Ch2/S2_Eq212.lean`. Route (TT:4384–4464):
* matrix layer: Takagi `B₁\bar U = UD` (`lemma_2_12` on the Hilbert–Schmidt operator of `B₁`, `cor_2_9`), singular
  sequence, `λ_n < 1` (HELD on `remark_2_3`), `V = B₂*U(I - D²)^{-1/2}` (`eq_2_2`, `grunsky_unitary`);
* kernel layer: `K₁, K₂, K₃, K₄` on `𝔲_n = Σ U_{mn}e_m`, `𝔳_n = Σ \bar V_{mn} f_m` (`e24_hK1`, `e24_hK4`, row series,
  pairings `e24_int_pair`, `e24_ext_pair`);
* principal values: `PV ∬ \bar𝔲/(ζ - η)² = 0` on `𝔻` and `𝔻*`; transport to `Ω = 𝖿(𝔻)`, `Ω* = 𝗀(𝔻*)` with Euclidean
  excision in `Ω`, `Ω*`;
* `e212_eq_2_12`: byte-identical copy of `eq_2_12`.

The principal-value block (`e212_pv_zero_disc` … `e212_pv_ext`, `e212_pv_gen` and its helpers) is by 下属3; the operator
layer uses `Ch2/S2_GrunskyOp` (`gop_`, 下属5).
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC
namespace Ch2

/-! ### Helpers -/

/-- A column of a matrix with orthonormal columns is square summable. -/
theorem e212_col_sq {W : ℕ → ℕ → ℂ} (hW : ∀ m n, (∑' k, conj (W k m) * W k n) = kron m n) (n : ℕ) :
    Summable fun k => ‖W k n‖ ^ 2 := by
  have h := hW n n
  simp only [kron] at h
  have hs : Summable fun k => conj (W k n) * W k n := by
    by_contra hns
    rw [tsum_eq_zero_of_not_summable hns] at h
    exact zero_ne_one h
  have he : (fun k => conj (W k n) * W k n) = fun k => ((‖W k n‖ ^ 2 : ℝ) : ℂ) := by
    funext k
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [he] at hs
  exact Complex.summable_ofReal.1 hs

theorem e212_inv_conformal : IsConformalOnto (fun z : ℂ => z⁻¹) unitDiscExterior (unitDisc \ {0}) := by
  refine ⟨?_, inv_injective.injOn, ?_⟩
  · intro z hz
    have hz0 : z ≠ 0 := by
      rintro rfl
      norm_num [unitDiscExterior] at hz
    exact (differentiableAt_inv hz0).differentiableWithinAt
  · ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact a21_inv_exterior hz
    · intro hw
      exact ⟨w⁻¹, a21_inv_punctured hw, inv_inv w⟩

/-- `Σ x_m f_m ∈ A₂¹(𝔻*)` for square-summable coefficients (inversion of `bergman_ell2_series`). -/
theorem e212_ext_series {x : ℕ → ℂ} (hx : Summable fun n => ‖x n‖ ^ 2) :
    (fun z => ∑' n, x n * basisF n z) ∈ A21fun unitDiscExterior := by
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hH := (bergman_ell2_series hx).1
  have hH' : (fun s => -∑' n, x n * basisE n s) ∈ A21fun (unitDisc \ {0}) := by
    have hneg := a21_const_mul measurableSet_ball hH (-1)
    refine ⟨(hneg.1.mono sdiff_subset).congr fun s _ => by ring, ?_⟩
    refine lt_of_le_of_lt ?_ hneg.2
    unfold normA21
    refine ENNReal.rpow_le_rpow (lintegral_mono_set sdiff_subset |>.trans_eq ?_) (by norm_num)
    refine lintegral_congr fun s => ?_
    show (‖-∑' n, x n * basisE n s‖₊ : ℝ≥0∞) ^ 2 = (‖-1 * ∑' n, x n * basisE n s‖₊ : ℝ≥0∞) ^ 2
    rw [neg_one_mul]
  have hp := a21_pullback hEo e212_inv_conformal hH'
  refine (ab112_A21fun_congr (U := unitDiscExterior) hEo ?_).1 hp
  intro z hz
  have hz0 : z ≠ 0 := by
    rintro rfl
    norm_num [unitDiscExterior] at hz
  show -(∑' n, x n * basisE n z⁻¹) * deriv (fun z : ℂ => z⁻¹) z = ∑' n, x n * basisF n z
  rw [deriv_inv, neg_mul, ← tsum_mul_right, ← tsum_neg]
  refine tsum_congr fun n => ?_
  have h := e24_basisF_inv n (inv_ne_zero hz0)
  rw [inv_inv] at h
  rw [h]
  field_simp

theorem e212_sq_summable (x : ell2) : Summable fun i => ‖x i‖ ^ 2 := by
  have h := (memℓp_gen_iff (p := 2) (by norm_num)).1 (lp.memℓp x)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h

/-- A column of a matrix with orthonormal columns has norm one. -/
theorem e212_col_norm {W : ℕ → ℕ → ℂ} (hW : ∀ m n, (∑' k, conj (W k m) * W k n) = kron m n) (n : ℕ) :
    ∑' k, ‖W k n‖ ^ 2 = 1 := by
  have h := hW n n
  simp only [kron, if_true] at h
  have he : (fun k => conj (W k n) * W k n) = fun k => ((‖W k n‖ ^ 2 : ℝ) : ℂ) := by
    funext k
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [he, ← Complex.ofReal_tsum] at h
  exact_mod_cast h

/-- `⟨w, Av⟩ = ⟨A*w, v⟩` for a bounded matrix, in coordinates: `Σ_k (Σ_p A_{kp} v_p) c_k = Σ_p v_p Σ_k A_{kp} c_k`. -/
theorem e212_swap {A : ℕ → ℕ → ℂ} (hrow : ∀ m, Summable fun n => ‖A m n‖ ^ 2)
    (hbd : ∃ C : ℝ, ∀ x : ℕ → ℂ, Summable (fun n => ‖x n‖ ^ 2) →
      ∀ M, ∑ m ∈ Finset.range M, ‖∑' n, A m n * x n‖ ^ 2 ≤ C * ∑' n, ‖x n‖ ^ 2)
    {v c : ℕ → ℂ} (hv : Summable fun p => ‖v p‖ ^ 2) (hc : Summable fun k => ‖c k‖ ^ 2) :
    HasSum (fun k => (∑' p, A k p * v p) * c k) (∑' p, v p * ∑' k, A k p * c k) := by
  let V : ell2 := ⟨v, memℓp_gen (by simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hv)⟩
  let W : ell2 := ⟨fun k => conj (c k), memℓp_gen (by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Complex.norm_conj] using hc)⟩
  have h1 := lp.hasSum_inner (𝕜 := ℂ) W (gopOp A V)
  have h2 : inner ℂ W (gopOp A V) = ∑' p, v p * ∑' k, A k p * c k := by
    rw [← ContinuousLinearMap.adjoint_inner_left, lp.inner_eq_tsum]
    refine tsum_congr fun p => ?_
    rw [gop_adjoint_apply hrow hbd, gop_inner_apply, Complex.conj_tsum, mul_comm]
    congr 1
    refine tsum_congr fun k => ?_
    show conj (conj (A k p) * conj (c k)) = A k p * c k
    rw [map_mul, Complex.conj_conj, Complex.conj_conj]
  rw [h2] at h1
  refine h1.congr_fun fun k => ?_
  rw [gop_apply hrow hbd, gop_inner_apply]
  show (∑' p, A k p * v p) * c k = conj (conj (c k)) * ∑' p, A k p * v p
  rw [Complex.conj_conj, mul_comm]

/-- Transport of a mixed-kernel identity `∬_D K(ζ, w) \bar a(w) = c b(ζ)`, `K = π⁻¹ G'(ζ)F'(η)/(G ζ - F η)²`, to
`(1/π) ∬_{F(D)} \overline{u(w)}/(z - w)² = c v(z)` on `G(E)`. -/
theorem e212_cross_gen {F G : ℂ → ℂ} {D E : Set ℂ} (hD : IsOpen D) (hE : IsOpen E)
    (hF : IsConformalOnto F D (F '' D)) (hG : IsConformalOnto G E (G '' E))
    (hdisj : ∀ ζ ∈ E, ∀ η ∈ D, G ζ ≠ F η) {a b : ℂ → ℂ} {c : ℂ} {K : ℂ → ℂ → ℂ}
    (hK : ∀ ζ ∈ E, ∀ η ∈ D, K ζ η = 1 / π * (deriv G ζ * deriv F η / (G ζ - F η) ^ 2))
    (hI : ∀ ζ ∈ E, (∫ w in D, K ζ w * conj (a w)) = c * b ζ) :
    ∀ z ∈ G '' E, 1 / π * (∫ w in F '' D,
        conj (a (Function.invFunOn F D w) * deriv (Function.invFunOn F D) w) / (z - w) ^ 2) =
      c * (b (Function.invFunOn G E z) * deriv (Function.invFunOn G E) z) := by
  rintro z ⟨ζ, hζ, rfl⟩
  have hlG : Function.invFunOn G E (G ζ) = ζ := hG.2.1.leftInvOn_invFunOn hζ
  have hdG := t1_deriv_invFunOn_mul hE hG hζ
  have hG0 : deriv G ζ ≠ 0 := right_ne_zero_of_mul_eq_one hdG
  have hiG : deriv (Function.invFunOn G E) (G ζ) = (deriv G ζ)⁻¹ := eq_inv_of_mul_eq_one_left hdG
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [hlG, hiG, ← mul_assoc, ← hI ζ hζ, ahP_integral_image hD hF.1 hF.2.1, ← integral_const_mul, ← integral_mul_const]
  refine setIntegral_congr_fun hD.measurableSet fun η hη => ?_
  have hlF : Function.invFunOn F D (F η) = η := hF.2.1.leftInvOn_invFunOn hη
  have hdF := t1_deriv_invFunOn_mul hD hF hη
  have hF0 : deriv F η ≠ 0 := right_ne_zero_of_mul_eq_one hdF
  have hiF : deriv (Function.invFunOn F D) (F η) = (deriv F η)⁻¹ := eq_inv_of_mul_eq_one_left hdF
  have hFc : conj (deriv F η) ≠ 0 := (map_ne_zero _).mpr hF0
  have hsub : G ζ - F η ≠ 0 := sub_ne_zero.mpr (hdisj ζ hζ η hη)
  have hn : (((‖deriv F η‖ ^ 2 : ℝ)) : ℂ) = deriv F η * conj (deriv F η) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hlF, hiF, hK ζ hζ η hη, Complex.real_smul, hn, map_mul, map_inv₀]
  field_simp

/-! ### Matrix layer: Takagi factorization, singular values, the partner unitary `V` (TT:4386–4425) -/

/-- Takagi factorization of the Hilbert–Schmidt symmetric `B₁` (`lemma_2_12` on the operator of `B₁`):
`B₁ \bar U = U D`, with `U` unitary (rows and columns orthonormal) and `D = diag(d)`, `d ≥ 0`. -/
theorem e212_takagi {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    (hHS : Summable fun q : ℕ × ℕ => ‖B1 (grunsky (fsans μ) (gsans μ)) q.1 q.2‖ ^ 2) :
    ∃ U : ℕ → ℕ → ℂ, ∃ d : ℕ → ℝ, (∀ n, 0 ≤ d n) ∧ (∀ m n, mulAdj U U m n = kron m n) ∧
      (∀ m n, (∑' k, conj (U k m) * U k n) = kron m n) ∧
      ∀ m n, HasSum (fun k => B1 (grunsky (fsans μ) (gsans μ)) m k * conj (U k n)) ((d n : ℂ) * U m n) := by
  classical
  have hpair := AppB.b8_welding_normalized_pair hμ
  have hF := r22_complement_null hμ
  have hsymA : ∀ m n, B1 (grunsky (fsans μ) (gsans μ)) m n = B1 (grunsky (fsans μ) (gsans μ)) n m :=
    fun m n => ((grunsky_unitary hpair hF).1 m n).1
  obtain ⟨hr1, hb1⟩ := gop_grunsky_bounds hpair hF (B1 (grunsky (fsans μ) (gsans μ))) (by simp)
  have hTc := gop_compact_of_HS hr1 hb1 hHS
  have hTx : ∀ (x : ell2) m, HasSum (fun k => B1 (grunsky (fsans μ) (gsans μ)) m k * x k)
      (gopOp (B1 (grunsky (fsans μ) (gsans μ))) x m) := fun x m => by
    rw [gop_apply hr1 hb1]
    exact (bergman_pair_summable (hr1 m) (e212_sq_summable x)).of_norm.hasSum
  obtain ⟨Uo, hU, D, d, hd, hD, hTU⟩ := lemma_2_12 hTc (gop_symm hr1 hb1 hsymA)
  have hUU : ∀ y, Uo (ContinuousLinearMap.adjoint Uo y) = y := fun y => by
    have h := congrArg (fun A : ell2 →L[ℂ] ell2 => A y) (Unitary.mul_star_self_of_mem hU)
    simpa [ContinuousLinearMap.star_eq_adjoint] using h
  have hUU' : ∀ y, ContinuousLinearMap.adjoint Uo (Uo y) = y := fun y => by
    have h := congrArg (fun A : ell2 →L[ℂ] ell2 => A y) (Unitary.star_mul_self_of_mem hU)
    simpa [ContinuousLinearMap.star_eq_adjoint] using h
  let e : ℕ → ell2 := fun n => lp.single 2 n (1 : ℂ)
  have hee : ∀ m n, inner ℂ (e m) (e n) = kron m n := fun m n => by
    rw [lp.inner_single_left, lp.single_apply, gop_inner_apply, map_one, one_mul, Pi.single_apply]
    rfl
  have hev : ∀ (y : ell2) n, inner ℂ (e n) y = y n := fun y n => by
    rw [lp.inner_single_left, gop_inner_apply, map_one, one_mul]
  refine ⟨fun m n => Uo (e n) m, d, hd, fun m n => ?_, fun m n => ?_, fun m n => ?_⟩
  · -- rows: `U_{mk} = \overline{(U* e_m)_k}`
    have hrowk : ∀ m k, Uo (e k) m = conj (ContinuousLinearMap.adjoint Uo (e m) k) := fun m k => by
      rw [← hev, ← hev (ContinuousLinearMap.adjoint Uo (e m)), ContinuousLinearMap.adjoint_inner_right,
        inner_conj_symm]
    have h := lp.hasSum_inner (𝕜 := ℂ) (ContinuousLinearMap.adjoint Uo (e m)) (ContinuousLinearMap.adjoint Uo (e n))
    rw [← ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_adjoint, hUU, hee] at h
    rw [mulAdj]
    refine h.tsum_eq ▸ tsum_congr fun k => ?_
    rw [hrowk m k, hrowk n k, Complex.conj_conj, gop_inner_apply]
  · -- columns
    have h := lp.hasSum_inner (𝕜 := ℂ) (Uo (e m)) (Uo (e n))
    rw [ContinuousLinearMap.inner_map_map_of_mem_unitary hU, hee] at h
    refine (tsum_congr fun k => ?_).trans h.tsum_eq
    rw [gop_inner_apply]
  · -- `B₁ \bar U = U D`, from `T x = U (D (Uᵗ x))` at `x = \overline{U e_n}`
    have hst : star (e n) = e n := by
      ext k
      simp only [e, lp.star_apply, lp.single_apply, Pi.single_apply]
      split_ifs <;> simp
    have htr : transposeOp Uo (star (Uo (e n))) = e n := by
      simp only [transposeOp, star_star, hUU', hst]
    have hDe : D (e n) = (d n : ℂ) • e n := by
      ext k
      rw [hD, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
      simp only [e, lp.single_apply, Pi.single_apply]
      split_ifs with h
      · subst h; simp
      · simp
    have hx := hTx (star (Uo (e n))) m
    rw [hTU, htr, hDe, map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul] at hx
    refine hx.congr_fun fun k => ?_
    rw [lp.star_apply]
    rfl

/-- The Takagi data give a singular value sequence: `B₁B₁* U = U D²`. -/
theorem e212_singular {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    (hHS : Summable fun q : ℕ × ℕ => ‖B1 (grunsky (fsans μ) (gsans μ)) q.1 q.2‖ ^ 2)
    {U : ℕ → ℕ → ℂ} {d : ℕ → ℝ} (hd : ∀ n, 0 ≤ d n) (hrow : ∀ m n, mulAdj U U m n = kron m n)
    (hcol : ∀ m n, (∑' k, conj (U k m) * U k n) = kron m n)
    (hBU : ∀ m n, HasSum (fun k => B1 (grunsky (fsans μ) (gsans μ)) m k * conj (U k n)) ((d n : ℂ) * U m n)) :
    IsSingularSeq (B1 (grunsky (fsans μ) (gsans μ))) d := by
  -- `hHS` is not needed: `B₁B₁*Ū`-columns are computed from the Takagi relation alone.
  have _h := hHS
  refine ⟨hd, U, hrow, hcol, fun m n => ?_⟩
  set b := grunsky (fsans μ) (gsans μ) with hbdef
  have hpair := AppB.b8_welding_normalized_pair hμ
  have hF := r22_complement_null hμ
  obtain ⟨hsy, -, -, -⟩ := grunsky_unitary hpair hF
  obtain ⟨hr1, hb1⟩ := gop_grunsky_bounds hpair hF (B1 b) (by simp [hbdef])
  have hr' : ∀ j, Summable fun k => ‖conj (B1 b k j)‖ ^ 2 := fun j =>
    (hr1 j).congr fun k => by rw [Complex.norm_conj, (hsy k j).1]
  have hb' : ∃ C : ℝ, ∀ x : ℕ → ℂ, Summable (fun n => ‖x n‖ ^ 2) →
      ∀ M, ∑ j ∈ Finset.range M, ‖∑' k, conj (B1 b k j) * x k‖ ^ 2 ≤ C * ∑' k, ‖x k‖ ^ 2 := by
    obtain ⟨C, hC⟩ := hb1
    refine ⟨C, fun x hx M => ?_⟩
    have h := hC (fun k => conj (x k)) (by simpa only [Complex.norm_conj] using hx) M
    simp only [Complex.norm_conj] at h
    refine le_of_eq_of_le (Finset.sum_congr rfl fun j _ => ?_) h
    rw [← Complex.norm_conj, Complex.conj_tsum]
    congr 2
    exact tsum_congr fun k => by rw [map_mul, Complex.conj_conj, (hsy k j).1]
  have hcj : ∀ j, (∑' k, conj (B1 b k j) * U k n) = (d n : ℂ) * conj (U j n) := fun j => by
    have h' := congrArg conj (hBU j n).tsum_eq
    rw [Complex.conj_tsum, map_mul, Complex.conj_ofReal] at h'
    rw [← h']
    exact tsum_congr fun k => by rw [map_mul, Complex.conj_conj, (hsy k j).1]
  have hS := e212_swap hr' hb' (e212_col_sq hcol n) (hr1 m)
  calc (∑' k, mulAdj (B1 b) (B1 b) m k * U k n)
      = ∑' k, U k n * ∑' j, conj (B1 b k j) * B1 b m j :=
        tsum_congr fun k => by
          rw [mulAdj, mul_comm]
          congr 1
          exact tsum_congr fun j => mul_comm _ _
    _ = ∑' j, (∑' k, conj (B1 b k j) * U k n) * B1 b m j := hS.tsum_eq.symm
    _ = ∑' j, (d n : ℂ) * (B1 b m j * conj (U j n)) := tsum_congr fun j => by rw [hcj j]; ring
    _ = ((d n ^ 2 : ℝ) : ℂ) * U m n := by
        rw [tsum_mul_left, (hBU m n).tsum_eq]
        push_cast
        ring

/-- `λ_n < 1` (HELD: from `remark_2_3`, `‖B₁x‖ ≤ c‖x‖` with `c < 1`, applied to the columns of `\bar U`). -/
theorem e212_lam_lt {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {U : ℕ → ℕ → ℂ} {d : ℕ → ℝ}
    (hcol : ∀ m n, (∑' k, conj (U k m) * U k n) = kron m n)
    (hBU : ∀ m n, HasSum (fun k => B1 (grunsky (fsans μ) (gsans μ)) m k * conj (U k n)) ((d n : ℂ) * U m n)) :
    ∀ n, d n < 1 := by
  intro n
  obtain ⟨c, hc0, hc1, C, hC⟩ := remark_2_3 hμ
  have hx := e212_col_sq hcol n
  have hxc : Summable fun k => ‖conj (U k n)‖ ^ 2 := by simpa only [Complex.norm_conj] using hx
  have hb := (hC (fun k => conj (U k n)) hxc).1
  have h1 : ∑' m, ‖∑' k, B1 (grunsky (fsans μ) (gsans μ)) m k * conj (U k n)‖ ^ 2 = d n ^ 2 := by
    have he : ∀ m, ‖∑' k, B1 (grunsky (fsans μ) (gsans μ)) m k * conj (U k n)‖ ^ 2 = d n ^ 2 * ‖U m n‖ ^ 2 :=
      fun m => by
        rw [(hBU m n).tsum_eq, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [tsum_congr he, tsum_mul_left, e212_col_norm hcol n, mul_one]
  have h2 : ∑' k, ‖conj (U k n)‖ ^ 2 = 1 := by
    simp only [Complex.norm_conj]
    exact e212_col_norm hcol n
  rw [h1, h2, mul_one] at hb
  by_contra hcon
  push Not at hcon
  nlinarith

/-- `V = B₂* U (I - D²)^{-1/2}` has orthonormal columns, and `B₂V = U ρ`, `B₃ \bar U = \bar V ρ`, `B₄V = -\bar V D`
(`ρ_n = √(1 - λ_n²)`; from `eq_2_2`, `grunsky_unitary`, `B₃ = B₂ᵗ`). -/
theorem e212_V {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {U : ℕ → ℕ → ℂ} {d : ℕ → ℝ} (hd : ∀ n, 0 ≤ d n)
    (hrow : ∀ m n, mulAdj U U m n = kron m n) (hcol : ∀ m n, (∑' k, conj (U k m) * U k n) = kron m n)
    (hBU : ∀ m n, HasSum (fun k => B1 (grunsky (fsans μ) (gsans μ)) m k * conj (U k n)) ((d n : ℂ) * U m n))
    (hlt : ∀ n, d n < 1) :
    ∃ V : ℕ → ℕ → ℂ, (∀ m n, (∑' k, conj (V k m) * V k n) = kron m n) ∧
      (∀ m n, HasSum (fun k => B2 (grunsky (fsans μ) (gsans μ)) m k * V k n)
        ((Real.sqrt (1 - d n ^ 2) : ℂ) * U m n)) ∧
      (∀ m n, HasSum (fun k => B3 (grunsky (fsans μ) (gsans μ)) m k * conj (U k n))
        ((Real.sqrt (1 - d n ^ 2) : ℂ) * conj (V m n))) ∧
      ∀ m n, HasSum (fun k => B4 (grunsky (fsans μ) (gsans μ)) m k * V k n) (-(d n : ℂ) * conj (V m n)) := by
  -- `hrow` is not needed (only the columns of `U` enter).
  have _hrow := hrow
  have hpair := AppB.b8_welding_normalized_pair hμ
  have hF := r22_complement_null hμ
  obtain ⟨hsy, -, -, -⟩ := grunsky_unitary hpair hF
  have hbs := gop_grunsky_bounds hpair hF
  obtain ⟨hr1, hb1⟩ := hbs (B1 (grunsky (fsans μ) (gsans μ))) (by simp)
  obtain ⟨hr2, hb2⟩ := hbs (B2 (grunsky (fsans μ) (gsans μ))) (by simp)
  obtain ⟨hr3, hb3⟩ := hbs (B3 (grunsky (fsans μ) (gsans μ))) (by simp)
  obtain ⟨hr4, hb4⟩ := hbs (B4 (grunsky (fsans μ) (gsans μ))) (by simp)
  obtain ⟨hblk1, -, hblk3, -⟩ := gop_blocks hpair hF
  set T1 := gopOp (B1 (grunsky (fsans μ) (gsans μ))) with hT1
  set T2 := gopOp (B2 (grunsky (fsans μ) (gsans μ))) with hT2
  set T3 := gopOp (B3 (grunsky (fsans μ) (gsans μ))) with hT3
  set T4 := gopOp (B4 (grunsky (fsans μ) (gsans μ))) with hT4
  have hblk3' : ∀ x, T3 (ContinuousLinearMap.adjoint T1 x) + T4 (ContinuousLinearMap.adjoint T2 x) = 0 := by
    intro x
    have h := congrArg ContinuousLinearMap.adjoint hblk3
    rw [map_add, map_zero, ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def,
      ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
      ContinuousLinearMap.adjoint_adjoint] at h
    have h' := congrArg (fun A : ell2 →L[ℂ] ell2 => A x) h
    simpa only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.zero_apply] using h'
  -- the columns of `U` as vectors
  have hU2 := e212_col_sq hcol
  let u : ℕ → ell2 := fun n => ⟨fun k => U k n,
    memℓp_gen (by simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hU2 n)⟩
  have hu : ∀ n k, u n k = U k n := fun n k => rfl
  have huu : ∀ m n, inner ℂ (u m) (u n) = kron m n := fun m n => by
    rw [lp.inner_eq_tsum, ← hcol m n]
    exact tsum_congr fun k => by rw [gop_inner_apply, hu, hu]
  -- `T₁ \bar u_n = d_n u_n` and `T₁* u_n = d_n \bar u_n`
  have hT1s : ∀ n, T1 (star (u n)) = (d n : ℂ) • u n := fun n => by
    ext m
    rw [hT1, gop_apply hr1 hb1, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, ← (hBU m n).tsum_eq]
    rfl
  have hT1a : ∀ n, ContinuousLinearMap.adjoint T1 (u n) = (d n : ℂ) • star (u n) := fun n => by
    ext p
    rw [hT1, gop_adjoint_apply hr1 hb1, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.star_apply]
    show ∑' m, conj (B1 (grunsky (fsans μ) (gsans μ)) m p) * U m n = (d n : ℂ) * conj (U p n)
    have h' := congrArg conj (hBU p n).tsum_eq
    rw [Complex.conj_tsum, map_mul, Complex.conj_ofReal] at h'
    rw [← h']
    exact tsum_congr fun k => by rw [map_mul, Complex.conj_conj, (hsy p k).1]
  -- `T₂T₂* u_n = (1 - d_n²) u_n`
  have hT22 : ∀ n, T2 (ContinuousLinearMap.adjoint T2 (u n)) = ((1 - d n ^ 2 : ℝ) : ℂ) • u n := fun n => by
    have h := congrArg (fun A : ell2 →L[ℂ] ell2 => A (u n)) hblk1
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] at h
    rw [hT1a, map_smul, hT1s, smul_smul] at h
    rw [eq_sub_of_add_eq' h]
    push_cast
    rw [sub_smul, one_smul, sq]
  have hρ : ∀ n, 0 < Real.sqrt (1 - d n ^ 2) := fun n =>
    Real.sqrt_pos.2 (by nlinarith [hd n, hlt n])
  have hρ2 : ∀ n, (Real.sqrt (1 - d n ^ 2)) ^ 2 = 1 - d n ^ 2 := fun n =>
    Real.sq_sqrt (by nlinarith [hd n, hlt n])
  have hρc : ∀ n, (Real.sqrt (1 - d n ^ 2) : ℂ) ≠ 0 := fun n => by exact_mod_cast (hρ n).ne'
  let v : ℕ → ell2 := fun n => ((Real.sqrt (1 - d n ^ 2) : ℂ)⁻¹) • ContinuousLinearMap.adjoint T2 (u n)
  have hv2 : ∀ n, Summable fun k => ‖v n k‖ ^ 2 := fun n => e212_sq_summable (v n)
  refine ⟨fun k n => v n k, fun m n => ?_, fun m n => ?_, fun m n => ?_, fun m n => ?_⟩
  · -- orthonormal columns
    have h1 : (∑' k, conj (v m k) * v n k) = inner ℂ (v m) (v n) := by
      rw [lp.inner_eq_tsum]
      exact tsum_congr fun k => by rw [gop_inner_apply]
    rw [h1]
    simp only [v]
    rw [inner_smul_left, inner_smul_right, ContinuousLinearMap.adjoint_inner_left, hT22, inner_smul_right, huu]
    by_cases hmn : m = n
    · subst hmn
      simp only [kron, if_true, mul_one, map_inv₀, Complex.conj_ofReal]
      have hc : ((Real.sqrt (1 - d m ^ 2) : ℝ) : ℂ) ^ 2 = 1 - (d m : ℂ) ^ 2 := by
        rw [← Complex.ofReal_pow, hρ2]; push_cast; ring
      push_cast
      field_simp [hρc m]
      first | linear_combination hc | linear_combination -hc
    · simp [kron, hmn]
  · -- `B₂ V = U ρ`
    have hsum := (bergman_pair_summable (hr2 m) (hv2 n)).of_norm.hasSum
    convert hsum using 1
    rw [← gop_apply hr2 hb2]
    show _ = (T2 (v n)) m
    simp only [v, map_smul, hT22, smul_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, hu]
    have hc : ((Real.sqrt (1 - d n ^ 2) : ℝ) : ℂ) ^ 2 = 1 - (d n : ℂ) ^ 2 := by
      rw [← Complex.ofReal_pow, hρ2]; push_cast; ring
    push_cast
    field_simp [hρc n]
    first | linear_combination U m n * hc | linear_combination -(U m n) * hc | linear_combination hc
  · -- `B₃ \bar U = \bar V ρ`
    have hsum := (bergman_pair_summable (hr3 m)
      (by simpa only [Complex.norm_conj] using hU2 n : Summable fun k => ‖conj (U k n)‖ ^ 2)).of_norm.hasSum
    convert hsum using 1
    show (Real.sqrt (1 - d n ^ 2) : ℂ) * conj (((Real.sqrt (1 - d n ^ 2) : ℂ)⁻¹) *
      ContinuousLinearMap.adjoint T2 (u n) m) = _
    rw [hT2, gop_adjoint_apply hr2 hb2, map_mul, map_inv₀, Complex.conj_ofReal, Complex.conj_tsum, ← mul_assoc,
      mul_inv_cancel₀ (hρc n), one_mul]
    refine tsum_congr fun k => ?_
    rw [map_mul, Complex.conj_conj, (hsy m k).2.2, hu]
  · -- `B₄ V = -\bar V D`
    have hsum := (bergman_pair_summable (hr4 m) (hv2 n)).of_norm.hasSum
    convert hsum using 1
    rw [← gop_apply hr4 hb4]
    show _ = (T4 (v n)) m
    have h4 : T4 (ContinuousLinearMap.adjoint T2 (u n)) = -((d n : ℂ) • T3 (star (u n))) := by
      have h := hblk3' (u n)
      rw [hT1a, map_smul] at h
      exact eq_neg_of_add_eq_zero_right h
    have h3 : ∀ q, T3 (star (u n)) q = (Real.sqrt (1 - d n ^ 2) : ℂ) * conj (v n q) := fun q => by
      rw [hT3, gop_apply hr3 hb3]
      show (∑' k, B3 (grunsky (fsans μ) (gsans μ)) q k * conj (U k n)) = _
      simp only [v, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
      rw [hT2, gop_adjoint_apply hr2 hb2, map_mul, map_inv₀, Complex.conj_ofReal, Complex.conj_tsum,
        ← mul_assoc, mul_inv_cancel₀ (hρc n), one_mul]
      refine tsum_congr fun k => ?_
      rw [map_mul, Complex.conj_conj, (hsy q k).2.2, hu]
    simp only [v, map_smul, h4, lp.coeFn_smul, lp.coeFn_neg, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, h3]
    simp only [map_mul, map_inv₀, Complex.conj_ofReal]
    field_simp [hρc n]

/-! ### Kernel layer: the operators `K_l` on the forms `𝔲_n`, `𝔳_n` (TT:4430–4440) -/

/-- `𝔲_n = Σ_m U_{mn} e_m ∈ A₂¹(𝔻)`, `𝔳_n = Σ_m \bar V_{mn} f_m ∈ A₂¹(𝔻*)`, and both families are orthonormal. -/
theorem e212_forms {U V : ℕ → ℕ → ℂ} (hcolU : ∀ m n, (∑' k, conj (U k m) * U k n) = kron m n)
    (hcolV : ∀ m n, (∑' k, conj (V k m) * V k n) = kron m n) :
    (∀ n, (fun z => ∑' m, U m n * basisE m z) ∈ A21fun unitDisc) ∧
      (∀ n, (fun z => ∑' m, conj (V m n) * basisF m z) ∈ A21fun unitDiscExterior) ∧
      (∀ m n, (∫ z in unitDisc, (∑' k, U k m * basisE k z) * conj (∑' k, U k n * basisE k z)) = kron m n) ∧
      ∀ m n, (∫ z in unitDiscExterior, (∑' k, conj (V k m) * basisF k z) *
        conj (∑' k, conj (V k n) * basisF k z)) = kron m n := by
  have hU2 := e212_col_sq hcolU
  have hV2 : ∀ n, Summable fun k => ‖conj (V k n)‖ ^ 2 := fun n => by
    simpa only [Complex.norm_conj] using e212_col_sq hcolV n
  have hkron : ∀ m n, kron m n = kron n m := fun m n => by
    unfold kron
    split_ifs with h1 h2 h2 <;> simp_all [eq_comm]
  have hE : ∀ (y : ℕ → ℂ), Summable (fun n => ‖y n‖ ^ 2) → ∀ u ∈ unitDisc,
      HasSum (fun n => y n * basisE n u) (∑' n, y n * basisE n u) := fun y hy u hu =>
    (bergman_pair_summable hy (basisE_sq_summable hu)).of_norm.hasSum
  refine ⟨fun n => (bergman_ell2_series (hU2 n)).1, fun n => e212_ext_series (hV2 n), fun m n => ?_,
    fun m n => ?_⟩
  · have h := A21_basis_pairing (bergman_ell2_series (hU2 m)).1 (bergman_ell2_series (hU2 n)).1
      (hE _ (hU2 m)) (hE _ (hU2 n))
    rw [← h.tsum_eq, hkron, ← hcolU n m]
    exact tsum_congr fun k => mul_comm _ _
  · have hF : ∀ (y : ℕ → ℂ), Summable (fun n => ‖y n‖ ^ 2) → ∀ z ∈ unitDiscExterior,
        HasSum (fun n => y n * basisF n z) (∑' n, y n * basisF n z) := by
      intro y hy z hz
      have hz0 : z ≠ 0 := by
        rintro rfl
        norm_num [unitDiscExterior] at hz
      have hu := a21_inv_exterior hz
      have hs := (bergman_pair_summable hy (basisE_sq_summable hu.1)).of_norm.mul_left (z⁻¹ ^ 2)
      refine (hs.congr fun n => ?_).hasSum
      have h := e24_basisF_inv n (inv_ne_zero hz0)
      rw [inv_inv] at h
      rw [h]
      ring
    have h := A21_basisF_pairing (e212_ext_series (hV2 m)) (e212_ext_series (hV2 n))
      (hF _ (hV2 m)) (hF _ (hV2 n))
    rw [← h.tsum_eq, ← hcolV m n]
    exact tsum_congr fun k => by rw [Complex.conj_conj]

/-- The four kernel identities: `K₁\bar𝔲 = λ𝔲`, `K₃\bar𝔲 = ρ𝔳`, `K₂\bar𝔳 = ρ𝔲`, `K₄\bar𝔳 = -λ𝔳`
(series `e24_hK1`/`e24_hK4` and the row expansions of `K₂`, `K₃`, paired by `e24_int_pair`/`e24_ext_pair`). -/
theorem e212_kernel {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    (hF : volume ((f '' unitDisc ∪ g '' unitDiscExterior)ᶜ) = 0) {U V : ℕ → ℕ → ℂ} {d : ℕ → ℝ}
    (hcolU : ∀ m n, (∑' k, conj (U k m) * U k n) = kron m n)
    (hcolV : ∀ m n, (∑' k, conj (V k m) * V k n) = kron m n)
    (h1 : ∀ m n, HasSum (fun k => B1 (grunsky f g) m k * conj (U k n)) ((d n : ℂ) * U m n))
    (h2 : ∀ m n, HasSum (fun k => B2 (grunsky f g) m k * V k n) ((Real.sqrt (1 - d n ^ 2) : ℂ) * U m n))
    (h3 : ∀ m n, HasSum (fun k => B3 (grunsky f g) m k * conj (U k n))
      ((Real.sqrt (1 - d n ^ 2) : ℂ) * conj (V m n)))
    (h4 : ∀ m n, HasSum (fun k => B4 (grunsky f g) m k * V k n) (-(d n : ℂ) * conj (V m n))) (n : ℕ) :
    (∀ z ∈ unitDisc, (∫ w in unitDisc, kerK1 f z w * conj (∑' m, U m n * basisE m w)) =
        (d n : ℂ) * ∑' m, U m n * basisE m z) ∧
      (∀ z ∈ unitDiscExterior, (∫ w in unitDisc, kerK3 f g z w * conj (∑' m, U m n * basisE m w)) =
        (Real.sqrt (1 - d n ^ 2) : ℂ) * ∑' m, conj (V m n) * basisF m z) ∧
      (∀ z ∈ unitDisc, (∫ w in unitDiscExterior, kerK2 f g z w * conj (∑' m, conj (V m n) * basisF m w)) =
        (Real.sqrt (1 - d n ^ 2) : ℂ) * ∑' m, U m n * basisE m z) ∧
      ∀ z ∈ unitDiscExterior, (∫ w in unitDiscExterior, kerK4 g z w * conj (∑' m, conj (V m n) * basisF m w)) =
        -(d n : ℂ) * ∑' m, conj (V m n) * basisF m z := by
  obtain ⟨hsy, hcolA, hcolB, -⟩ := grunsky_unitary h hF
  have hb := gop_grunsky_bounds h hF
  obtain ⟨hr1, hb1⟩ := hb (B1 (grunsky f g)) (by simp)
  obtain ⟨hr2, hb2⟩ := hb (B2 (grunsky f g)) (by simp)
  obtain ⟨hr3, hb3⟩ := hb (B3 (grunsky f g)) (by simp)
  obtain ⟨hr4, hb4⟩ := hb (B4 (grunsky f g)) (by simp)
  have hU2 := e212_col_sq hcolU n
  have hU2c : Summable fun k => ‖conj (U k n)‖ ^ 2 := by simpa only [Complex.norm_conj] using hU2
  have hV2 := e212_col_sq hcolV n
  have hV2c : Summable fun k => ‖conj (V k n)‖ ^ 2 := by simpa only [Complex.norm_conj] using hV2
  have hV2cc : Summable fun k => ‖conj (conj (V k n))‖ ^ 2 := by
    simpa only [Complex.norm_conj] using hV2
  have h𝔲 : ∀ u ∈ unitDisc, HasSum (fun m => U m n * basisE m u) (∑' m, U m n * basisE m u) :=
    fun u hu => (bergman_pair_summable hU2 (basisE_sq_summable hu)).of_norm.hasSum
  have h𝔳 : ∀ u ∈ unitDiscExterior,
      HasSum (fun m => conj (V m n) * basisF m u) (∑' m, conj (V m n) * basisF m u) :=
    fun u hu => (bergman_pair_summable hV2c (e24_sq_of_abs (e24_absF hu))).of_norm.hasSum
  refine ⟨fun z hz => ?_, fun z hz => ?_, fun z hz => ?_, fun z hz => ?_⟩
  · -- `K₁`
    obtain ⟨hx, -⟩ := e24_pair_sq (v := fun p => basisE p z) hcolA (e24_absE hz)
    have hexp : ∀ u ∈ unitDisc, u ∉ ({z} : Set ℂ) →
        HasSum (fun k => (∑' p, B1 (grunsky f g) k p * basisE p z) * basisE k u) (kerK1 f z u) :=
      fun u hu hn => g2c_kernel_row_series (fun m n => (hsy m n).1) (e24_hK1 h) hz hu
        (fun h0 => hn (by simp [h0])) fun k => (bergman_pair_summable (hr1 k) (basisE_sq_summable hz)).of_norm
    have hI := e24_int_pair hx hU2 ((Set.finite_singleton z).measure_zero volume) hexp (fun u hu _ => h𝔲 u hu)
    have hS := e212_swap hr1 hb1 (basisE_sq_summable hz) hU2c
    rw [hI.unique hS, ← tsum_mul_left]
    refine tsum_congr fun p => ?_
    have hc : (∑' k, B1 (grunsky f g) k p * conj (U k n)) = (d n : ℂ) * U p n := by
      rw [← (h1 p n).tsum_eq]
      exact tsum_congr fun k => by rw [(hsy k p).1]
    rw [hc]
    ring
  · -- `K₃`
    obtain ⟨hx, -⟩ := e24_pair_sq (v := fun p => basisF p z) hcolB (e24_absF hz)
    have hexp : ∀ u ∈ unitDisc, u ∉ (∅ : Set ℂ) →
        HasSum (fun k => (∑' q, B2 (grunsky f g) k q * basisF q z) * basisE k u) (kerK3 f g z u) := by
      intro u hu _
      rw [e24_K3_eq]
      refine (e24_K2_series h hu hz).prod_fiberwise (fun k => ?_)
      refine (((bergman_pair_summable (hr2 k) (e24_sq_of_abs (e24_absF hz))).of_norm).hasSum.mul_right
        (basisE k u)).congr_fun (fun q => ?_)
      ring
    have hI := e24_int_pair hx hU2 measure_empty hexp (fun u hu _ => h𝔲 u hu)
    have hS := e212_swap hr2 hb2 (e24_sq_of_abs (e24_absF hz)) hU2c
    rw [hI.unique hS, ← tsum_mul_left]
    refine tsum_congr fun q => ?_
    have hc : (∑' k, B2 (grunsky f g) k q * conj (U k n)) =
        (Real.sqrt (1 - d n ^ 2) : ℂ) * conj (V q n) := by
      rw [← (h3 q n).tsum_eq]
      exact tsum_congr fun k => by rw [(hsy q k).2.2]
    rw [hc]
    ring
  · -- `K₂`
    obtain ⟨-, hx⟩ := e24_pair_sq (v := fun p => basisE p z) hcolA (e24_absE hz)
    have hexp : ∀ u ∈ unitDiscExterior, u ∉ (∅ : Set ℂ) →
        HasSum (fun q => (∑' p, B3 (grunsky f g) q p * basisE p z) * basisF q u) (kerK2 f g z u) := by
      intro u hu _
      have hs := (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr (e24_K2_series h hz hu)
      refine hs.prod_fiberwise (fun q => ?_)
      refine (((bergman_pair_summable (hr3 q) (basisE_sq_summable hz)).of_norm).hasSum.mul_right
        (basisF q u)).congr_fun (fun p => ?_)
      simp only [Function.comp_apply, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
      rw [(hsy q p).2.2]
    have hI := e24_ext_pair hx hV2c Set.finite_empty hexp (fun u hu _ => h𝔳 u hu)
    have hS := e212_swap hr3 hb3 (basisE_sq_summable hz) hV2cc
    rw [hI.unique hS, ← tsum_mul_left]
    refine tsum_congr fun p => ?_
    have hc : (∑' q, B3 (grunsky f g) q p * conj (conj (V q n))) =
        (Real.sqrt (1 - d n ^ 2) : ℂ) * U p n := by
      rw [← (h2 p n).tsum_eq]
      exact tsum_congr fun q => by rw [(hsy q p).2.2, Complex.conj_conj]
    rw [hc]
    ring
  · -- `K₄`
    obtain ⟨-, hx⟩ := e24_pair_sq (v := fun p => basisF p z) hcolB (e24_absF hz)
    have hexp : ∀ u ∈ unitDiscExterior, u ∉ ({z} : Set ℂ) →
        HasSum (fun q => (∑' p, B4 (grunsky f g) q p * basisF p z) * basisF q u) (kerK4 g z u) := by
      intro u hu hn
      have hne : z ≠ u := fun h0 => hn (by simp [h0])
      have hs := (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr (e24_hK4 h hF z hz u hu hne)
      refine hs.prod_fiberwise (fun q => ?_)
      refine (((bergman_pair_summable (hr4 q) (e24_sq_of_abs (e24_absF hz))).of_norm).hasSum.mul_right
        (basisF q u)).congr_fun (fun p => ?_)
      simp only [Function.comp_apply, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
      rw [(hsy q p).2.1]
    have hI := e24_ext_pair hx hV2c (Set.finite_singleton z) hexp (fun u hu _ => h𝔳 u hu)
    have hS := e212_swap hr4 hb4 (e24_sq_of_abs (e24_absF hz)) hV2cc
    rw [hI.unique hS, ← tsum_mul_left]
    refine tsum_congr fun p => ?_
    have hc : (∑' q, B4 (grunsky f g) q p * conj (conj (V q n))) = -(d n : ℂ) * conj (V p n) := by
      rw [← (h4 p n).tsum_eq]
      exact tsum_congr fun q => by rw [(hsy q p).2.1, Complex.conj_conj]
    rw [hc]
    ring

/-! ### Principal values (TT:4444–4464) -/

/-- `PV ∬_𝔻 \overline{𝔲(η)}/(ζ - η)² d²η = 0` for `𝔲 ∈ A₂¹(𝔻)`, `ζ ∈ 𝔻` (round excision). -/
theorem e212_pv_zero_disc {𝔲 : ℂ → ℂ} (h𝔲 : 𝔲 ∈ A21fun unitDisc) {ζ : ℂ} (hζ : ζ ∈ unitDisc) :
    Tendsto (fun δ : ℝ => ∫ η in unitDisc \ ball ζ δ, conj (𝔲 η) / (ζ - η) ^ 2) (𝓝[>] 0) (𝓝 0) := by
  exact remark_2_4 h𝔲 hζ

/-- Area change of variables under `w ↦ 1/w` on a measurable set avoiding `0`. -/
theorem e212_cov_inv {S : Set ℂ} (hS : MeasurableSet S) (hS0 : ∀ w ∈ S, w ≠ 0) (F : ℂ → ℂ) :
    (∫ η in (fun w : ℂ => w⁻¹) '' S, F η) =
      ∫ w in S, ((‖-(w ^ 2)⁻¹‖ ^ 2 : ℝ) : ℂ) * F w⁻¹ := by
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hS
    (fun w hw => ((hasDerivAt_inv (hS0 w hw)).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt)
    inv_injective.injOn F]
  apply setIntegral_congr_fun hS
  intro w _
  dsimp only
  rw [det_restrictScalars_toSpanSingleton, abs_of_nonneg (sq_nonneg _)]
  simp [Complex.real_smul]

/-- The pointwise identity behind the inversion: `|(1/w)'|² \overline{a}/(ζ - 1/w)² = -z² \overline{a·(-1/w²)}/(z - w)²`
with `z = 1/ζ`. -/
theorem e212_inv_integrand {a ζ w : ℂ} (hw : w ≠ 0) (hζ : ζ ≠ 0) :
    ((‖-(w ^ 2)⁻¹‖ ^ 2 : ℝ) : ℂ) * (conj a / (ζ - w⁻¹) ^ 2) =
      -(ζ⁻¹) ^ 2 * (conj (a * -(w ^ 2)⁻¹) / (ζ⁻¹ - w) ^ 2) := by
  have h1 : ((‖w‖ ^ 2 : ℝ) : ℂ) = w * conj w := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hn : ((‖-(w ^ 2)⁻¹‖ ^ 2 : ℝ) : ℂ) = ((w * conj w) ^ 2)⁻¹ := by
    rw [← h1, norm_neg, norm_inv, norm_pow]
    push_cast
    ring
  rw [hn]
  have hcw : conj w ≠ 0 := (map_ne_zero _).2 hw
  by_cases hzw : ζ⁻¹ = w
  · have h2 : ζ - w⁻¹ = 0 := by rw [← hzw, inv_inv, sub_self]
    rw [h2, hzw, sub_self]
    simp
  · have h2 : ζ⁻¹ - w ≠ 0 := sub_ne_zero.mpr hzw
    have h3 : ζ - w⁻¹ = (w - ζ⁻¹) * ζ / w := by field_simp
    rw [h3, map_mul, map_neg, map_inv₀, map_pow]
    have h4 : w - ζ⁻¹ ≠ 0 := fun h => h2 (by rw [← neg_sub, h, neg_zero])
    field_simp
    ring

/-- Area change of variables under a conformal map, on a measurable subset of the domain. -/
theorem e212_cov_conf {f : ℂ → ℂ} {U S : Set ℂ} (hU : IsOpen U) (hd : DifferentiableOn ℂ f U)
    (hi : InjOn f U) (hS : MeasurableSet S) (hSU : S ⊆ U) (g : ℂ → ℂ) :
    (∫ w in f '' S, g w) = ∫ η in S, ((‖deriv f η‖ ^ 2 : ℝ) : ℂ) * g (f η) := by
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hS
    (fun z hz => ((hd.differentiableAt (hU.mem_nhds (hSU hz))).hasDerivAt.hasFDerivAt.restrictScalars
      ℝ).hasFDerivWithinAt) (hi.mono hSU) g]
  apply setIntegral_congr_fun hS
  intro z _
  dsimp only
  rw [det_restrictScalars_toSpanSingleton, abs_of_nonneg (sq_nonneg _)]
  simp [Complex.real_smul]

/-- Open mapping: a univalent map of `D` covers a ball about `f(ζ)` by any ball about `ζ` inside `D`. -/
theorem e212_open_ball {f : ℂ → ℂ} {D : Set ℂ} (hd : DifferentiableOn ℂ f D) (hi : InjOn f D)
    {ζ : ℂ} {r : ℝ} (hr : 0 < r) (hsub : ball ζ r ⊆ D) :
    ∃ ε > 0, ball (f ζ) ε ⊆ f '' ball ζ r := by
  have han := (hd.mono hsub).analyticOnNhd isOpen_ball
  rcases han.is_constant_or_isOpen (convex_ball ζ r).isPreconnected with ⟨w, hw⟩ | ho
  · exfalso
    have h0 : ζ ∈ ball ζ r := mem_ball_self hr
    have h1 : ζ + ((r / 2 : ℝ) : ℂ) ∈ ball ζ r := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      linarith
    have h2 := hi (hsub h0) (hsub h1) (by rw [hw _ h0, hw _ h1])
    have h3 : ((r / 2 : ℝ) : ℂ) = 0 := by linear_combination -h2
    have h4 : r / 2 = 0 := by exact_mod_cast h3
    linarith
  · have hO := ho (ball ζ r) subset_rfl isOpen_ball
    obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.mp hO (f ζ) ⟨ζ, mem_ball_self hr, rfl⟩
    exact ⟨ε, hε, hb⟩

/-- `‖u‖² ∈ L¹(D)` for `u ∈ A₂¹(D)`. -/
theorem e212_sq_integrable {D : Set ℂ} (hDo : IsOpen D) {u : ℂ → ℂ} (hu : u ∈ A21fun D) :
    IntegrableOn (fun η => ‖u η‖ ^ 2) D := by
  refine ⟨(hu.1.continuousOn.norm.pow 2).aestronglyMeasurable hDo.measurableSet, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ => by positivity)]
  have h := a21_sq_lintegral_ne_top hu
  refine lt_of_le_of_lt (le_of_eq ?_) h.lt_top
  apply lintegral_congr
  intro η
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rfl

/-- Truncated integrability: `ar u/(ζ - η)² ∈ L¹(D ∖ B(ζ, ρ))` for `u ∈ A₂¹(D)`. -/
theorem e212_trunc_int {D : Set ℂ} (hDo : IsOpen D) {u : ℂ → ℂ} (hu : u ∈ A21fun D) (ζ : ℂ) {ρ : ℝ}
    (hρ : 0 < ρ) : IntegrableOn (fun η => conj (u η) / (ζ - η) ^ 2) (D \ ball ζ ρ) := by
  have hm : MeasurableSet (D \ ball ζ ρ) := hDo.measurableSet.diff measurableSet_ball
  have hfar : ∀ η ∈ D \ ball ζ ρ, ρ ≤ ‖η - ζ‖ := fun η hη => by
    simpa [mem_ball, dist_eq_norm] using hη.2
  have hc : ContinuousOn (fun η => conj (u η) / (ζ - η) ^ 2) (D \ ball ζ ρ) :=
    (Complex.continuous_conj.comp_continuousOn (hu.1.continuousOn.mono sdiff_subset)).div
      ((continuousOn_const.sub continuousOn_id).pow 2)
      (fun η hη => pow_ne_zero 2 (by
        intro h
        have := hfar η hη
        rw [← norm_neg, neg_sub, h, norm_zero] at this
        linarith))
  have h4 : IntegrableOn (fun η : ℂ => (‖η - ζ‖ ^ 4)⁻¹) (D \ ball ζ ρ) :=
    (s2c_l4_outside_ball ζ hρ).1.mono_set (fun η hη => hfar η hη)
  refine Integrable.mono' (((e212_sq_integrable hDo hu).mono_set sdiff_subset).add h4 |>.div_const 2)
    (hc.aestronglyMeasurable hm) ?_
  rw [ae_restrict_iff' hm]
  refine Eventually.of_forall fun η hη => ?_
  have hn : 0 < ‖η - ζ‖ := lt_of_lt_of_le hρ (hfar η hη)
  simp only [Pi.add_apply]
  rw [norm_div, Complex.norm_conj, norm_pow, ← norm_neg (ζ - η), neg_sub]
  have e1 : (‖η - ζ‖ ^ 4)⁻¹ = (1 / ‖η - ζ‖ ^ 2) ^ 2 := by field_simp
  have e2 : ‖u η‖ / ‖η - ζ‖ ^ 2 = ‖u η‖ * (1 / ‖η - ζ‖ ^ 2) := by field_simp
  rw [e1, e2]
  nlinarith [sq_nonneg (‖u η‖ - 1 / ‖η - ζ‖ ^ 2)]

/-- The pointwise pull-back identity: `|b|² \overline{u b⁻¹}/(f ζ - f η)² = a⁻¹(\bar u/(ζ - η)² - π K₁ \bar u)`. -/
theorem e212_pull_integrand {a b u fz fe ζ η : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) (hne : ζ - η ≠ 0)
    (hf : fz - fe ≠ 0) :
    ((‖b‖ ^ 2 : ℝ) : ℂ) * (conj (u * b⁻¹) / (fz - fe) ^ 2) =
      a⁻¹ * (conj u / (ζ - η) ^ 2 - π * (1 / π * (1 / (ζ - η) ^ 2 - a * b / (fz - fe) ^ 2) * conj u)) := by
  have hn : ((‖b‖ ^ 2 : ℝ) : ℂ) = b * conj b := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hcb : conj b ≠ 0 := (map_ne_zero _).2 hb
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [hn, map_mul, map_inv₀]
  field_simp
  ring

/-- `K₁(ζ, ·) \bar𝔲` is integrable on `𝔻`: bounded near `ζ`, and `|f'|²/|f - f(ζ)|⁴ ∈ L¹` away from `ζ`. -/
theorem e212_K1_integrable {D : Set ℂ} (hDo : IsOpen D) {f : ℂ → ℂ} (hf : IsConformalOnto f D (f '' D))
    {𝔲 : ℂ → ℂ} (h𝔲 : 𝔲 ∈ A21fun D) {ζ : ℂ} (hζ : ζ ∈ D) :
    IntegrableOn (fun η => kerK1 f ζ η * conj (𝔲 η)) D := by
  have hd := hf.1
  have hi := hf.2.1
  obtain ⟨R, hR, hRb⟩ := Metric.isOpen_iff.mp hDo ζ hζ
  obtain ⟨r, hrd⟩ : ∃ r : ℝ, r = R / 2 := ⟨_, rfl⟩
  have hr : 0 < r := by rw [hrd]; linarith
  have hcl : closedBall ζ r ⊆ D := (closedBall_subset_ball (by rw [hrd]; linarith)).trans hRb
  have hK1d := AppB.differentiableOn_kerK1_right hDo hd hi hζ
  have hU1 : IntegrableOn (fun η => kerK1 f ζ η * conj (𝔲 η)) (closedBall ζ r) :=
    ((hK1d.continuousOn.mono hcl).mul
      (Complex.continuous_conj.comp_continuousOn (h𝔲.1.continuousOn.mono hcl))).integrableOn_compact
      (isCompact_closedBall ζ r)
  -- the far part
  obtain ⟨V, hVd⟩ : ∃ V : Set ℂ, V = D \ closedBall ζ r := ⟨_, rfl⟩
  have hVo : IsOpen V := by rw [hVd]; exact hDo.sdiff isClosed_closedBall
  have hVD : V ⊆ D := by rw [hVd]; exact sdiff_subset
  have hVm : MeasurableSet V := hVo.measurableSet
  have hVne : ∀ η ∈ V, ζ ≠ η := by
    intro η hη h
    rw [hVd] at hη
    exact hη.2 (h ▸ mem_closedBall_self hr.le)
  obtain ⟨ε, hε, hεb⟩ := e212_open_ball hd hi hr (ball_subset_closedBall.trans hcl)
  have hfar : ∀ η ∈ V, ε ≤ ‖f η - f ζ‖ := by
    intro η hη
    by_contra hlt
    push Not at hlt
    obtain ⟨η', hη', he⟩ := hεb (by rw [mem_ball, dist_eq_norm]; exact hlt)
    have := hi (hcl (ball_subset_closedBall hη')) (hVD hη) he
    rw [hVd] at hη
    exact hη.2 (this ▸ ball_subset_closedBall hη')
  have hfne : ∀ η ∈ V, f ζ - f η ≠ 0 := by
    intro η hη h
    have := hfar η hη
    rw [← norm_neg, neg_sub, h, norm_zero] at this
    linarith
  have hu2 : IntegrableOn (fun η => ‖𝔲 η‖ ^ 2) D := e212_sq_integrable hDo h𝔲
  -- `|f'|²/|f - f(ζ)|⁴ ∈ L¹(V)`
  have hd4 : IntegrableOn (fun η => ‖deriv f η‖ ^ 2 * (‖f η - f ζ‖ ^ 4)⁻¹) V := by
    have hc : ContinuousOn (fun η => ‖deriv f η‖ ^ 2 * (‖f η - f ζ‖ ^ 4)⁻¹) V :=
      ((((hd.deriv hDo).continuousOn.mono hVD).norm.pow 2).mul
        ((((hd.continuousOn.mono hVD).sub continuousOn_const).norm.pow 4).inv₀
          (fun η hη => pow_ne_zero 4 (lt_of_lt_of_le hε (hfar η hη)).ne')))
    refine ⟨hc.aestronglyMeasurable hVm, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ => by positivity)]
    have hcov := d2_lintegral_image hVo (hd.mono hVD) (hi.mono hVD)
      (fun w => ENNReal.ofReal ((‖w - f ζ‖ ^ 4)⁻¹))
    have heq : (∫⁻ η in V, ENNReal.ofReal (‖deriv f η‖ ^ 2 * (‖f η - f ζ‖ ^ 4)⁻¹)) =
        ∫⁻ η in V, ENNReal.ofReal (‖deriv f η‖ ^ 2) * ENNReal.ofReal ((‖f η - f ζ‖ ^ 4)⁻¹) := by
      apply lintegral_congr
      intro η
      rw [ENNReal.ofReal_mul (by positivity)]
    rw [heq, ← hcov]
    have hsub : f '' V ⊆ {w : ℂ | ε ≤ ‖w - f ζ‖} := by
      rintro _ ⟨η, hη, rfl⟩
      exact hfar η hη
    have hfin := (s2c_l4_outside_ball (f ζ) hε).1.lintegral_lt_top
    exact lt_of_le_of_lt (lintegral_mono_set hsub) hfin
  -- the cross term `f' \bar𝔲/(f ζ - f η)²`
  have hC : IntegrableOn (fun η => deriv f η * conj (𝔲 η) / (f ζ - f η) ^ 2) V := by
    have hc : ContinuousOn (fun η => deriv f η * conj (𝔲 η) / (f ζ - f η) ^ 2) V :=
      (((hd.deriv hDo).continuousOn.mono hVD).mul
        (Complex.continuous_conj.comp_continuousOn (h𝔲.1.continuousOn.mono hVD))).div
        ((continuousOn_const.sub (hd.continuousOn.mono hVD)).pow 2)
        (fun η hη => pow_ne_zero 2 (hfne η hη))
    refine Integrable.mono' ((hd4.add (hu2.mono_set hVD)).div_const 2) (hc.aestronglyMeasurable hVm) ?_
    rw [ae_restrict_iff' hVm]
    refine Eventually.of_forall fun η hη => ?_
    have hn : 0 < ‖f η - f ζ‖ := lt_of_lt_of_le hε (hfar η hη)
    simp only [Pi.add_apply]
    rw [norm_div, norm_mul, Complex.norm_conj, norm_pow, ← norm_neg (f ζ - f η), neg_sub]
    have e1 : ‖deriv f η‖ ^ 2 * (‖f η - f ζ‖ ^ 4)⁻¹ = (‖deriv f η‖ / ‖f η - f ζ‖ ^ 2) ^ 2 := by
      field_simp
    have e2 : ‖deriv f η‖ * ‖𝔲 η‖ / ‖f η - f ζ‖ ^ 2 = (‖deriv f η‖ / ‖f η - f ζ‖ ^ 2) * ‖𝔲 η‖ := by
      field_simp
    rw [e1, e2]
    nlinarith [sq_nonneg (‖deriv f η‖ / ‖f η - f ζ‖ ^ 2 - ‖𝔲 η‖)]
  -- on `V`, `K₁ \bar𝔲 = π⁻¹ \bar𝔲/(ζ - η)² - π⁻¹ f'(ζ) · (cross term)`
  have hA : IntegrableOn (fun η => conj (𝔲 η) / (ζ - η) ^ 2) V :=
    (e212_trunc_int hDo h𝔲 ζ hr).mono_set (by
      rw [hVd]; exact sdiff_subset_sdiff_right ball_subset_closedBall)
  have hU2 : IntegrableOn (fun η => kerK1 f ζ η * conj (𝔲 η)) V := by
    have hs : IntegrableOn (fun η => 1 / (π : ℂ) * (conj (𝔲 η) / (ζ - η) ^ 2) -
        1 / π * deriv f ζ * (deriv f η * conj (𝔲 η) / (f ζ - f η) ^ 2)) V :=
      (hA.const_mul (1 / π : ℂ)).sub (hC.const_mul (1 / π * deriv f ζ))
    refine IntegrableOn.congr_fun hs ?_ hVm
    intro η hη
    show _ = kerK1 f ζ η * conj (𝔲 η)
    rw [kerK1_of_ne f (hVne η hη)]
    ring
  have hcover : D ⊆ closedBall ζ r ∪ V := by
    intro η hη
    by_cases h : η ∈ closedBall ζ r
    · exact Or.inl h
    · exact Or.inr (by rw [hVd]; exact ⟨hη, h⟩)
  exact (hU1.union hU2).mono_set hcover

/-- `volume (B(ζ, s)) = π s²`. -/
theorem e212_volume_ball (ζ : ℂ) {s : ℝ} (hs : 0 ≤ s) : volume (ball ζ s) = ENNReal.ofReal (π * s ^ 2) := by
  rw [Complex.volume_ball, ENNReal.ofReal_mul Real.pi_pos.le, ENNReal.ofReal_pow hs,
    ← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
  exact mul_comm _ _

/-- The crescent bound: `‖∬_{O ∖ B(ζ, ρ₁)} \bar u/(ζ - w)²‖ ≤ (M/ρ₁²) π(ρ₂² - ρ₁²)` for `O ⊆ B(ζ, ρ₂)`, `|u| ≤ M` on `O`. -/
theorem e212_crescent {u : ℂ → ℂ} {ζ : ℂ} {O : Set ℂ} {ρ1 ρ2 M : ℝ} (hO : O ⊆ ball ζ ρ2)
    (hρ1 : 0 < ρ1) (hρ12 : ρ1 ≤ ρ2) (hM0 : 0 ≤ M) (hM : ∀ w ∈ O, ‖u w‖ ≤ M) :
    ‖∫ w in O \ ball ζ ρ1, conj (u w) / (ζ - w) ^ 2‖ ≤ M / ρ1 ^ 2 * (π * ρ2 ^ 2 - π * ρ1 ^ 2) := by
  have hT : O \ ball ζ ρ1 ⊆ ball ζ ρ2 \ ball ζ ρ1 := fun w hw => ⟨hO hw.1, hw.2⟩
  have hbd : ∀ w ∈ O \ ball ζ ρ1, ‖conj (u w) / (ζ - w) ^ 2‖ ≤ M / ρ1 ^ 2 := by
    intro w hw
    have hd1 : ρ1 ≤ ‖ζ - w‖ := by
      rw [norm_sub_rev]
      simpa [mem_ball, dist_eq_norm] using hw.2
    rw [norm_div, Complex.norm_conj, norm_pow]
    have hzw : 0 < ‖ζ - w‖ ^ 2 := by have := hρ1.trans_le hd1; positivity
    rw [div_le_div_iff₀ hzw (by positivity)]
    calc ‖u w‖ * ρ1 ^ 2 ≤ M * ρ1 ^ 2 := mul_le_mul_of_nonneg_right (hM w hw.1) (by positivity)
      _ ≤ M * ‖ζ - w‖ ^ 2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ1.le hd1 2) hM0
  have hvolT : volume (O \ ball ζ ρ1) ≤ ENNReal.ofReal (π * ρ2 ^ 2 - π * ρ1 ^ 2) := by
    calc volume (O \ ball ζ ρ1) ≤ volume (ball ζ ρ2 \ ball ζ ρ1) := measure_mono hT
      _ = volume (ball ζ ρ2) - volume (ball ζ ρ1) :=
          measure_sdiff (ball_subset_ball hρ12) measurableSet_ball.nullMeasurableSet
            measure_ball_lt_top.ne
      _ = ENNReal.ofReal (π * ρ2 ^ 2 - π * ρ1 ^ 2) := by
          rw [e212_volume_ball ζ (hρ1.le.trans hρ12), e212_volume_ball ζ hρ1.le,
            ENNReal.ofReal_sub _ (by positivity)]
  have hTfin : volume (O \ ball ζ ρ1) < ∞ := lt_of_le_of_lt hvolT ENNReal.ofReal_lt_top
  have hvr : (volume (O \ ball ζ ρ1)).toReal ≤ π * ρ2 ^ 2 - π * ρ1 ^ 2 :=
    ENNReal.toReal_le_of_le_ofReal
      (sub_nonneg.mpr (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ1.le hρ12 2) Real.pi_pos.le)) hvolT
  calc ‖∫ w in O \ ball ζ ρ1, conj (u w) / (ζ - w) ^ 2‖
      ≤ M / ρ1 ^ 2 * (volume (O \ ball ζ ρ1)).toReal := norm_setIntegral_le_of_norm_le_const hTfin hbd
    _ ≤ M / ρ1 ^ 2 * (π * ρ2 ^ 2 - π * ρ1 ^ 2) := mul_le_mul_of_nonneg_left hvr (by positivity)

/-- `‖∬_O F‖ ≤ N π ρ²` for `O ⊆ B(ζ, ρ)`, `|F| ≤ N` on `O`. -/
theorem e212_small {F : ℂ → ℂ} {ζ : ℂ} {O : Set ℂ} {ρ N : ℝ} (hO : O ⊆ ball ζ ρ) (hρ : 0 ≤ ρ)
    (hN0 : 0 ≤ N) (hN : ∀ w ∈ O, ‖F w‖ ≤ N) : ‖∫ w in O, F w‖ ≤ N * (π * ρ ^ 2) := by
  have hvolO : volume O ≤ ENNReal.ofReal (π * ρ ^ 2) := (measure_mono hO).trans (e212_volume_ball ζ hρ).le
  have hOfin : volume O < ∞ := lt_of_le_of_lt hvolO ENNReal.ofReal_lt_top
  have hvr : (volume O).toReal ≤ π * ρ ^ 2 := ENNReal.toReal_le_of_le_ofReal (by positivity) hvolO
  calc ‖∫ w in O, F w‖ ≤ N * (volume O).toReal := norm_setIntegral_le_of_norm_le_const hOfin hN
    _ ≤ N * (π * ρ ^ 2) := mul_le_mul_of_nonneg_left hvr hN0

/-- Bracketing of the pulled-back excision `f⁻¹(B(f(ζ), δ))` between `B(ζ, t(1 - kt))` and `B(ζ, t(1 + 4kt))`,
`t = δ/|f'(ζ)|` (second-order Taylor bound and open mapping). -/
theorem e212_bracket {D : Set ℂ} (hDo : IsOpen D) {f : ℂ → ℂ} (hf : IsConformalOnto f D (f '' D))
    {ζ : ℂ} (hζ : ζ ∈ D) :
    ∃ r > 0, closedBall ζ r ⊆ D ∧ ∃ k > 0, ∀ᶠ δ : ℝ in 𝓝[>] 0, k * (δ / ‖deriv f ζ‖) ≤ 1 / 8 ∧
      ball ζ (δ / ‖deriv f ζ‖ * (1 - k * (δ / ‖deriv f ζ‖))) ⊆ D ∩ f ⁻¹' ball (f ζ) δ ∧
      D ∩ f ⁻¹' ball (f ζ) δ ⊆ ball ζ (δ / ‖deriv f ζ‖ * (1 + 4 * k * (δ / ‖deriv f ζ‖))) ∧
      δ / ‖deriv f ζ‖ * (1 + 4 * k * (δ / ‖deriv f ζ‖)) ≤ r := by
  have hd := hf.1
  have hi := hf.2.1
  obtain ⟨a, had⟩ : ∃ a : ℂ, a = deriv f ζ := ⟨_, rfl⟩
  rw [← had]
  have ha : a ≠ 0 := by rw [had]; exact deriv_ne_zero_of_injOn hDo hd hi hζ
  have ha0 : 0 < ‖a‖ := norm_pos_iff.mpr ha
  obtain ⟨R, hR, hRb⟩ := Metric.isOpen_iff.mp hDo ζ hζ
  obtain ⟨r, hrd⟩ : ∃ r : ℝ, r = R / 2 := ⟨_, rfl⟩
  have hr : 0 < r := by rw [hrd]; linarith
  have hcl : closedBall ζ r ⊆ D := (closedBall_subset_ball (by rw [hrd]; linarith)).trans hRb
  refine ⟨r, hr, hcl, ?_⟩
  -- `f η - f ζ = (η - ζ)(a + (η - ζ) q(η))`, `|q| ≤ C` near `ζ`
  obtain ⟨q, hqd⟩ : ∃ q : ℂ → ℂ, q = dslope (dslope f ζ) ζ := ⟨_, rfl⟩
  have hdd : DifferentiableOn ℂ (dslope f ζ) D :=
    (Complex.differentiableOn_dslope (hDo.mem_nhds hζ)).mpr hd
  have hqdiff : DifferentiableOn ℂ q D := by
    rw [hqd]; exact (Complex.differentiableOn_dslope (hDo.mem_nhds hζ)).mpr hdd
  have hexp : ∀ η : ℂ, f η - f ζ = (η - ζ) * (a + (η - ζ) * q η) := by
    intro η
    have h1 : f η - f ζ = (η - ζ) * dslope f ζ η := by
      simpa only [smul_eq_mul] using (sub_smul_dslope f ζ η).symm
    have h2 := sub_smul_dslope (dslope f ζ) ζ η
    rw [dslope_same, smul_eq_mul, ← hqd, ← had] at h2
    rw [h1]
    congr 1
    linear_combination -h2
  obtain ⟨Cq, hCq⟩ := (isCompact_closedBall ζ r).exists_bound_of_continuousOn
    (hqdiff.continuousOn.mono hcl)
  obtain ⟨C, hCd⟩ : ∃ C : ℝ, C = max Cq 1 := ⟨_, rfl⟩
  have hC1 : 1 ≤ C := by rw [hCd]; exact le_max_right _ _
  have hC0 : 0 < C := by linarith
  have hqC : ∀ η ∈ closedBall ζ r, ‖q η‖ ≤ C := fun η hη =>
    (hCq η hη).trans (by rw [hCd]; exact le_max_left _ _)
  have hup : ∀ η ∈ closedBall ζ r, ‖f η - f ζ‖ ≤ ‖η - ζ‖ * (‖a‖ + C * ‖η - ζ‖) := by
    intro η hη
    rw [hexp, norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    calc ‖a + (η - ζ) * q η‖ ≤ ‖a‖ + ‖η - ζ‖ * ‖q η‖ := by
          rw [← norm_mul]; exact norm_add_le _ _
      _ ≤ ‖a‖ + C * ‖η - ζ‖ := by nlinarith [hqC η hη, norm_nonneg (η - ζ)]
  have hlow : ∀ η ∈ closedBall ζ r, ‖η - ζ‖ * (‖a‖ - C * ‖η - ζ‖) ≤ ‖f η - f ζ‖ := by
    intro η hη
    rw [hexp, norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    have h1 := norm_sub_norm_le a (-((η - ζ) * q η))
    rw [sub_neg_eq_add, norm_neg, norm_mul] at h1
    nlinarith [hqC η hη, norm_nonneg (η - ζ)]
  -- the open-mapping radius and the constants
  obtain ⟨r', hr'd⟩ : ∃ r' : ℝ, r' = min r (‖a‖ / (2 * C)) := ⟨_, rfl⟩
  have hr' : 0 < r' := by rw [hr'd]; exact lt_min hr (by positivity)
  have hr'r : r' ≤ r := by rw [hr'd]; exact min_le_left _ _
  have hr'a : r' ≤ ‖a‖ / (2 * C) := by rw [hr'd]; exact min_le_right _ _
  obtain ⟨ε, hε, hεb⟩ := e212_open_ball hd hi hr'
    ((ball_subset_ball hr'r).trans (ball_subset_closedBall.trans hcl))
  obtain ⟨k, hkd⟩ : ∃ k : ℝ, k = C / ‖a‖ := ⟨_, rfl⟩
  have hk : 0 < k := by rw [hkd]; positivity
  have hkC : C = k * ‖a‖ := by rw [hkd]; field_simp
  refine ⟨k, hk, ?_⟩
  have hsm : ∀ᶠ δ : ℝ in 𝓝[>] 0, k * (δ / ‖a‖) ≤ 1 / 8 ∧
      δ / ‖a‖ * (1 + 4 * k * (δ / ‖a‖)) ≤ r' ∧ δ < ε := by
    have h1 : Tendsto (fun δ : ℝ => k * (δ / ‖a‖)) (𝓝 0) (𝓝 0) := by
      have := ((tendsto_id (x := 𝓝 (0 : ℝ))).div_const ‖a‖).const_mul k
      simpa using this
    have h2 : Tendsto (fun δ : ℝ => δ / ‖a‖ * (1 + 4 * k * (δ / ‖a‖))) (𝓝 0) (𝓝 0) := by
      have hc : Continuous (fun δ : ℝ => δ / ‖a‖ * (1 + 4 * k * (δ / ‖a‖))) := by fun_prop
      have := hc.tendsto 0
      simpa using this
    exact ((h1.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8))).and
      ((h2.eventually (ge_mem_nhds hr')).and (gt_mem_nhds hε))).filter_mono nhdsWithin_le_nhds
  filter_upwards [hsm, self_mem_nhdsWithin] with δ hδs hδ0
  obtain ⟨hkt, hρ2r', hδε⟩ := hδs
  have hδ : 0 < δ := hδ0
  obtain ⟨t, htd⟩ : ∃ t : ℝ, t = δ / ‖a‖ := ⟨_, rfl⟩
  have ht : 0 < t := by rw [htd]; positivity
  have hδt : δ = ‖a‖ * t := by rw [htd]; field_simp
  rw [← htd] at hkt hρ2r' ⊢
  have hu0 : 0 < k * t := by positivity
  have hρ1 : 0 < t * (1 - k * t) := by nlinarith
  have hρ2r : t * (1 + 4 * k * t) ≤ r := hρ2r'.trans hr'r
  have hρ2a : t * (1 + 4 * k * t) ≤ ‖a‖ / (2 * C) := hρ2r'.trans hr'a
  have hρ12 : t * (1 - k * t) ≤ t * (1 + 4 * k * t) := by nlinarith
  have hmemO : ∀ η, η ∈ D ∩ f ⁻¹' ball (f ζ) δ ↔ η ∈ D ∧ ‖f η - f ζ‖ < δ := by
    intro η
    rw [mem_inter_iff, mem_preimage, mem_ball, dist_eq_norm]
  refine ⟨hkt, ?_, ?_, hρ2r⟩
  · intro η hη
    have hs : ‖η - ζ‖ < t * (1 - k * t) := by simpa [mem_ball, dist_eq_norm] using hη
    have hηc : η ∈ closedBall ζ r := by
      rw [mem_closedBall, dist_eq_norm]; linarith
    refine (hmemO η).mpr ⟨hcl hηc, ?_⟩
    have h1 := hup η hηc
    have h2 : ‖η - ζ‖ * (‖a‖ + C * ‖η - ζ‖) < t * (1 - k * t) * (‖a‖ + C * (t * (1 - k * t))) :=
      calc ‖η - ζ‖ * (‖a‖ + C * ‖η - ζ‖) ≤ ‖η - ζ‖ * (‖a‖ + C * (t * (1 - k * t))) :=
            mul_le_mul_of_nonneg_left (by nlinarith) (norm_nonneg _)
        _ < t * (1 - k * t) * (‖a‖ + C * (t * (1 - k * t))) := mul_lt_mul_of_pos_right hs (by positivity)
    have h3 : t * (1 - k * t) * (‖a‖ + C * (t * (1 - k * t))) ≤ δ := by
      rw [hkC, hδt]
      have e : t * (1 - k * t) * (‖a‖ + k * ‖a‖ * (t * (1 - k * t))) =
          ‖a‖ * t * ((1 - k * t) * (1 + k * t * (1 - k * t))) := by ring
      rw [e]
      have e4 : 1 - (1 - k * t) * (1 + k * t * (1 - k * t)) = (k * t) ^ 2 * (2 - k * t) := by ring
      have h4 : (1 - k * t) * (1 + k * t * (1 - k * t)) ≤ 1 := by
        have : 0 ≤ (k * t) ^ 2 * (2 - k * t) := mul_nonneg (sq_nonneg _) (by linarith)
        linarith
      exact mul_le_of_le_one_right (by positivity) h4
    linarith
  · intro η hη
    obtain ⟨hηD, hηb⟩ := (hmemO η).mp hη
    obtain ⟨η', hη', he⟩ := hεb (show f η ∈ ball (f ζ) ε by
      rw [mem_ball, dist_eq_norm]; linarith)
    have hη'D : η' ∈ D := hcl (ball_subset_closedBall (ball_subset_ball hr'r hη'))
    have hee : η' = η := hi hη'D hηD he
    rw [hee] at hη'
    have hs : ‖η - ζ‖ < r' := by simpa [mem_ball, dist_eq_norm] using hη'
    rw [mem_ball, dist_eq_norm]
    by_contra hge
    push Not at hge
    have hηc : η ∈ closedBall ζ r := by
      rw [mem_closedBall, dist_eq_norm]; linarith
    have h1 := hlow η hηc
    have h2 : t * (1 + 4 * k * t) * (‖a‖ - C * (t * (1 + 4 * k * t))) ≤
        ‖η - ζ‖ * (‖a‖ - C * ‖η - ζ‖) := by
      have hsa : ‖η - ζ‖ ≤ ‖a‖ / (2 * C) := hs.le.trans hr'a
      have e1 : C * (‖a‖ / (2 * C)) = ‖a‖ / 2 := by field_simp
      have hsum : C * (‖η - ζ‖ + t * (1 + 4 * k * t)) ≤ ‖a‖ := by
        have h5 := mul_le_mul_of_nonneg_left hsa hC0.le
        have h6 := mul_le_mul_of_nonneg_left hρ2a hC0.le
        rw [e1] at h5 h6
        linarith
      have e : ‖η - ζ‖ * (‖a‖ - C * ‖η - ζ‖) - t * (1 + 4 * k * t) * (‖a‖ - C * (t * (1 + 4 * k * t))) =
          (‖η - ζ‖ - t * (1 + 4 * k * t)) * (‖a‖ - C * (‖η - ζ‖ + t * (1 + 4 * k * t))) := by ring
      have : 0 ≤ (‖η - ζ‖ - t * (1 + 4 * k * t)) * (‖a‖ - C * (‖η - ζ‖ + t * (1 + 4 * k * t))) :=
        mul_nonneg (sub_nonneg.mpr hge) (by linarith)
      linarith
    have h3 : δ ≤ t * (1 + 4 * k * t) * (‖a‖ - C * (t * (1 + 4 * k * t))) := by
      rw [hkC, hδt]
      have e : t * (1 + 4 * k * t) * (‖a‖ - k * ‖a‖ * (t * (1 + 4 * k * t))) =
          ‖a‖ * t * ((1 + 4 * k * t) * (1 - k * t * (1 + 4 * k * t))) := by ring
      rw [e]
      have e4 : (1 + 4 * k * t) * (1 - k * t * (1 + 4 * k * t)) - 1 =
          k * t * (3 - 8 * (k * t) - 16 * (k * t) ^ 2) := by ring
      have h4 : 1 ≤ (1 + 4 * k * t) * (1 - k * t * (1 + 4 * k * t)) := by
        have h7 : 0 ≤ 3 - 8 * (k * t) - 16 * (k * t) ^ 2 := by nlinarith
        have : 0 ≤ k * t * (3 - 8 * (k * t) - 16 * (k * t) ^ 2) := mul_nonneg hu0.le h7
        linarith
      exact le_mul_of_one_le_right (by positivity) h4
    linarith

/-- The pulled-back identity: `(1/π) ∬_{Ω ∖ B(f ζ, δ)} \bar u/(f ζ - w)² = (π f'(ζ))⁻¹ ∬_{𝔻∖O} \bar𝔲/(ζ - η)²
- f'(ζ)⁻¹ ∬_{𝔻∖O} K₁(ζ, η) \bar𝔲`, `O = D ∩ f⁻¹(B(f ζ, δ)) ⊇ B(ζ, ρ)`. -/
theorem e212_identity {D : Set ℂ} (hDo : IsOpen D) {f : ℂ → ℂ} (hf : IsConformalOnto f D (f '' D))
    {𝔲 : ℂ → ℂ} (h𝔲 : 𝔲 ∈ A21fun D) {lam ζ : ℂ} (hζ : ζ ∈ D)
    (hKζ : (∫ w in D, kerK1 f ζ w * conj (𝔲 w)) = lam * 𝔲 ζ) {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ)
    (hB : ball ζ ρ ⊆ D ∩ f ⁻¹' ball (f ζ) δ) :
    (1 / π * ∫ w in f '' D \ ball (f ζ) δ,
        conj (𝔲 (Function.invFunOn f D w) * deriv (Function.invFunOn f D) w) / (f ζ - w) ^ 2) =
      1 / π * (deriv f ζ)⁻¹ * ((∫ η in D \ ball ζ ρ, conj (𝔲 η) / (ζ - η) ^ 2) -
        ∫ η in (D ∩ f ⁻¹' ball (f ζ) δ) \ ball ζ ρ, conj (𝔲 η) / (ζ - η) ^ 2) -
      (deriv f ζ)⁻¹ * (lam * 𝔲 ζ - ∫ η in D ∩ f ⁻¹' ball (f ζ) δ, kerK1 f ζ η * conj (𝔲 η)) := by
  have hd := hf.1
  have hi := hf.2.1
  have hlF : ∀ η ∈ D, Function.invFunOn f D (f η) = η := fun η hη =>
    hi.leftInvOn_invFunOn hη
  have hdFi : ∀ η ∈ D, deriv (Function.invFunOn f D) (f η) = (deriv f η)⁻¹ := fun η hη =>
    eq_inv_of_mul_eq_one_left (t1_deriv_invFunOn_mul hDo hf hη)
  have hder : ∀ η ∈ D, deriv f η ≠ 0 := fun η hη => deriv_ne_zero_of_injOn hDo hd hi hη
  have hBint := e212_K1_integrable hDo hf h𝔲 hζ
  obtain ⟨a, had⟩ : ∃ a : ℂ, a = deriv f ζ := ⟨_, rfl⟩
  rw [← had]
  have ha : a ≠ 0 := by rw [had]; exact hder ζ hζ
  obtain ⟨O, hOd⟩ : ∃ O : Set ℂ, O = D ∩ f ⁻¹' ball (f ζ) δ := ⟨_, rfl⟩
  rw [← hOd] at hB ⊢
  have hOo : IsOpen O := by rw [hOd]; exact hd.continuousOn.isOpen_inter_preimage hDo isOpen_ball
  have hOm : MeasurableSet O := hOo.measurableSet
  have hOD : O ⊆ D := by rw [hOd]; exact inter_subset_left
  have hmemO : ∀ η, η ∈ O ↔ η ∈ D ∧ f η ∈ ball (f ζ) δ := by
    intro η
    rw [hOd, mem_inter_iff, mem_preimage]
  have hζO : ζ ∈ O := (hmemO ζ).mpr ⟨hζ, mem_ball_self hδ⟩
  obtain ⟨S, hSd⟩ : ∃ S : Set ℂ, S = D \ O := ⟨_, rfl⟩
  have hSm : MeasurableSet S := by rw [hSd]; exact hDo.measurableSet.diff hOm
  have hSD : S ⊆ D := by rw [hSd]; exact sdiff_subset
  have himg : f '' S = f '' D \ ball (f ζ) δ := by
    ext w
    constructor
    · rintro ⟨η, hη, rfl⟩
      rw [hSd] at hη
      exact ⟨⟨η, hη.1, rfl⟩, fun hb => hη.2 ((hmemO η).mpr ⟨hη.1, hb⟩)⟩
    · rintro ⟨⟨η, hηD, rfl⟩, hnb⟩
      refine ⟨η, ?_, rfl⟩
      rw [hSd]
      exact ⟨hηD, fun hO => hnb ((hmemO η).mp hO).2⟩
  rw [← himg, e212_cov_conf hDo hd hi hSm hSD]
  have hpt : ∀ η ∈ S, ((‖deriv f η‖ ^ 2 : ℝ) : ℂ) *
      (conj (𝔲 (Function.invFunOn f D (f η)) * deriv (Function.invFunOn f D) (f η)) /
        (f ζ - f η) ^ 2) =
      a⁻¹ * (conj (𝔲 η) / (ζ - η) ^ 2 - π * (kerK1 f ζ η * conj (𝔲 η))) := by
    intro η hη
    rw [hSd] at hη
    have hηD := hη.1
    have hζη : ζ ≠ η := fun h => hη.2 (h ▸ hζO)
    have hfne : f ζ - f η ≠ 0 := fun h => hζη (hi hζ hηD (sub_eq_zero.mp h))
    rw [hlF η hηD, hdFi η hηD, kerK1_of_ne f hζη, ← had]
    exact e212_pull_integrand ha (hder η hηD) (sub_ne_zero.mpr hζη) hfne
  have hSsub : S ⊆ D \ ball ζ ρ := by
    rw [hSd]; exact sdiff_subset_sdiff_right hB
  have hA1 : IntegrableOn (fun η => conj (𝔲 η) / (ζ - η) ^ 2) (D \ ball ζ ρ) :=
    e212_trunc_int hDo h𝔲 ζ hρ
  have hAS : IntegrableOn (fun η => conj (𝔲 η) / (ζ - η) ^ 2) S := hA1.mono_set hSsub
  have hBS : IntegrableOn (fun η => kerK1 f ζ η * conj (𝔲 η)) S := hBint.mono_set hSD
  have hBS' : IntegrableOn (fun η => (π : ℂ) * (kerK1 f ζ η * conj (𝔲 η))) S :=
    Integrable.const_mul hBS (π : ℂ)
  have hsplit0 : (∫ η in S, a⁻¹ * (conj (𝔲 η) / (ζ - η) ^ 2 - π * (kerK1 f ζ η * conj (𝔲 η)))) =
      a⁻¹ * ((∫ η in S, conj (𝔲 η) / (ζ - η) ^ 2) - π * ∫ η in S, kerK1 f ζ η * conj (𝔲 η)) := by
    rw [integral_const_mul, integral_sub hAS hBS', integral_const_mul]
  rw [setIntegral_congr_fun hSm hpt, hsplit0]
  have hsplit : S = (D \ ball ζ ρ) \ (O \ ball ζ ρ) := by
    rw [hSd]
    ext w
    simp only [Set.mem_sdiff]
    constructor
    · rintro ⟨hwD, hwO⟩
      exact ⟨⟨hwD, fun h => hwO (hB h)⟩, fun h => hwO h.1⟩
    · rintro ⟨⟨hwD, hwB⟩, hw⟩
      exact ⟨hwD, fun h => hw ⟨h, hwB⟩⟩
  have hA2 : ∫ η in S, conj (𝔲 η) / (ζ - η) ^ 2 =
      (∫ η in D \ ball ζ ρ, conj (𝔲 η) / (ζ - η) ^ 2) -
        ∫ η in O \ ball ζ ρ, conj (𝔲 η) / (ζ - η) ^ 2 := by
    rw [hsplit, setIntegral_sdiff (hOm.diff measurableSet_ball) hA1 (fun w hw => ⟨hOD hw.1, hw.2⟩)]
  have hB2 : ∫ η in S, kerK1 f ζ η * conj (𝔲 η) = lam * 𝔲 ζ - ∫ η in O, kerK1 f ζ η * conj (𝔲 η) := by
    rw [hSd, setIntegral_sdiff hOm hBint hOD, hKζ]
  rw [hA2, hB2]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hπ1 : (1 / (π : ℂ)) * π = 1 := one_div_mul_cancel hπ
  linear_combination (-(a⁻¹ * (lam * 𝔲 ζ - ∫ η in O, kerK1 f ζ η * conj (𝔲 η)))) * hπ1

/-- Transport of a `K₁`-type eigenform to `f(D)` with Euclidean excision, given the principal value
`PV ∬_D \bar𝔲/(ζ - η)² = 0` on `D`. -/
theorem e212_pv_gen {D : Set ℂ} (hDo : IsOpen D) {f : ℂ → ℂ} (hf : IsConformalOnto f D (f '' D))
    {𝔲 : ℂ → ℂ} (h𝔲 : 𝔲 ∈ A21fun D) {lam : ℂ}
    (hK : ∀ ζ ∈ D, (∫ w in D, kerK1 f ζ w * conj (𝔲 w)) = lam * 𝔲 ζ)
    (hPV : ∀ ζ ∈ D, Tendsto (fun δ : ℝ => ∫ η in D \ ball ζ δ, conj (𝔲 η) / (ζ - η) ^ 2) (𝓝[>] 0) (𝓝 0)) :
    ∀ z ∈ f '' D, Tendsto (fun δ : ℝ => 1 / π * ∫ w in f '' D \ ball z δ,
        conj (𝔲 (Function.invFunOn f D w) * deriv (Function.invFunOn f D) w) / (z - w) ^ 2)
      (𝓝[>] 0) (𝓝 (-lam * (𝔲 (Function.invFunOn f D z) * deriv (Function.invFunOn f D) z))) := by
  rintro _ ⟨ζ, hζ, rfl⟩
  have hd := hf.1
  have hi := hf.2.1
  rw [hi.leftInvOn_invFunOn hζ, eq_inv_of_mul_eq_one_left (t1_deriv_invFunOn_mul hDo hf hζ)]
  obtain ⟨r, hr, hcl, k, hk, hev⟩ := e212_bracket hDo hf hζ
  have ha0 : 0 < ‖deriv f ζ‖ := norm_pos_iff.mpr (deriv_ne_zero_of_injOn hDo hd hi hζ)
  obtain ⟨M0, hM0⟩ := (isCompact_closedBall ζ r).exists_bound_of_continuousOn
    (h𝔲.1.continuousOn.mono hcl)
  obtain ⟨M, hMd⟩ : ∃ M : ℝ, M = max M0 0 := ⟨_, rfl⟩
  have hM0' : 0 ≤ M := by rw [hMd]; exact le_max_right _ _
  have hM : ∀ η ∈ closedBall ζ r, ‖𝔲 η‖ ≤ M := fun η hη =>
    (hM0 η hη).trans (by rw [hMd]; exact le_max_left _ _)
  have hBc : ContinuousOn (fun η => kerK1 f ζ η * conj (𝔲 η)) (closedBall ζ r) :=
    ((AppB.differentiableOn_kerK1_right hDo hd hi hζ).continuousOn.mono hcl).mul
      (Complex.continuous_conj.comp_continuousOn (h𝔲.1.continuousOn.mono hcl))
  obtain ⟨N0, hN0⟩ := (isCompact_closedBall ζ r).exists_bound_of_continuousOn hBc
  obtain ⟨N, hNd⟩ : ∃ N : ℝ, N = max N0 0 := ⟨_, rfl⟩
  have hN0' : 0 ≤ N := by rw [hNd]; exact le_max_right _ _
  have hN : ∀ η ∈ closedBall ζ r, ‖kerK1 f ζ η * conj (𝔲 η)‖ ≤ N := fun η hη =>
    (hN0 η hη).trans (by rw [hNd]; exact le_max_left _ _)
  obtain ⟨ρ1, hρ1d⟩ : ∃ ρ1 : ℝ → ℝ, ρ1 = fun δ => δ / ‖deriv f ζ‖ * (1 - k * (δ / ‖deriv f ζ‖)) :=
    ⟨_, rfl⟩
  obtain ⟨ρ2, hρ2d⟩ : ∃ ρ2 : ℝ → ℝ, ρ2 = fun δ => δ / ‖deriv f ζ‖ * (1 + 4 * k * (δ / ‖deriv f ζ‖)) :=
    ⟨_, rfl⟩
  have hρ1c : Continuous ρ1 := by rw [hρ1d]; fun_prop
  have hρ2c : Continuous ρ2 := by rw [hρ2d]; fun_prop
  have hρ10 : ρ1 0 = 0 := by rw [hρ1d]; simp
  have hρ20 : ρ2 0 = 0 := by rw [hρ2d]; simp
  have hmain : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      (1 / π * ∫ w in f '' D \ ball (f ζ) δ,
        conj (𝔲 (Function.invFunOn f D w) * deriv (Function.invFunOn f D) w) / (f ζ - w) ^ 2) =
        1 / π * (deriv f ζ)⁻¹ * ((∫ η in D \ ball ζ (ρ1 δ), conj (𝔲 η) / (ζ - η) ^ 2) -
          ∫ η in (D ∩ f ⁻¹' ball (f ζ) δ) \ ball ζ (ρ1 δ), conj (𝔲 η) / (ζ - η) ^ 2) -
        (deriv f ζ)⁻¹ * (lam * 𝔲 ζ - ∫ η in D ∩ f ⁻¹' ball (f ζ) δ, kerK1 f ζ η * conj (𝔲 η)) ∧
      ‖∫ η in (D ∩ f ⁻¹' ball (f ζ) δ) \ ball ζ (ρ1 δ), conj (𝔲 η) / (ζ - η) ^ 2‖ ≤
        16 * π * M * k * (δ / ‖deriv f ζ‖) ∧
      ‖∫ η in D ∩ f ⁻¹' ball (f ζ) δ, kerK1 f ζ η * conj (𝔲 η)‖ ≤ N * (π * ρ2 δ ^ 2) ∧
      0 < ρ1 δ := by
    filter_upwards [hev, self_mem_nhdsWithin] with δ hδs hδ0
    obtain ⟨hkt, hB1, hB2, hρ2r⟩ := hδs
    have hδ : 0 < δ := hδ0
    obtain ⟨t, htd⟩ : ∃ t : ℝ, t = δ / ‖deriv f ζ‖ := ⟨_, rfl⟩
    have ht : 0 < t := by rw [htd]; positivity
    have hρ1v : ρ1 δ = t * (1 - k * t) := by rw [hρ1d, htd]
    have hρ2v : ρ2 δ = t * (1 + 4 * k * t) := by rw [hρ2d, htd]
    rw [← htd] at hkt hB1 hB2 hρ2r ⊢
    rw [← hρ1v] at hB1
    rw [← hρ2v] at hB2 hρ2r
    have hu0 : 0 < k * t := by positivity
    have hρ1 : 0 < ρ1 δ := by rw [hρ1v]; nlinarith
    have hρ12 : ρ1 δ ≤ ρ2 δ := by rw [hρ1v, hρ2v]; nlinarith
    have hO2r : D ∩ f ⁻¹' ball (f ζ) δ ⊆ closedBall ζ r := fun η hη =>
      ball_subset_closedBall (ball_subset_ball hρ2r (hB2 hη))
    refine ⟨e212_identity hDo hf h𝔲 hζ (hK ζ hζ) hδ hρ1 hB1, ?_,
      e212_small hB2 (hρ1.le.trans hρ12) hN0' (fun w hw => hN w (hO2r hw)), hρ1⟩
    have hc := e212_crescent hB2 hρ1 hρ12 hM0' (fun w hw => hM w (hO2r hw)) (u := 𝔲)
    have hratio : ρ2 δ ^ 2 - ρ1 δ ^ 2 ≤ 16 * (k * t) * ρ1 δ ^ 2 := by
      rw [hρ1v, hρ2v]
      have hu1 : k * t ≤ 1 / 8 := hkt
      have e : (t * (1 + 4 * k * t)) ^ 2 - (t * (1 - k * t)) ^ 2 =
          t ^ 2 * (k * t) * (10 + 15 * (k * t)) := by ring
      have e2 : 16 * (k * t) * (t * (1 - k * t)) ^ 2 = t ^ 2 * (k * t) * (16 * (1 - k * t) ^ 2) := by ring
      rw [e, e2]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [sq_nonneg (k * t)]
    calc _ ≤ M / ρ1 δ ^ 2 * (π * ρ2 δ ^ 2 - π * ρ1 δ ^ 2) := hc
      _ = π * M * ((ρ2 δ ^ 2 - ρ1 δ ^ 2) / ρ1 δ ^ 2) := by field_simp
      _ ≤ π * M * (16 * (k * t)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [div_le_iff₀ (by positivity)]
          exact hratio
      _ = 16 * π * M * k * t := by ring
  -- the limits
  have hρ1w : Tendsto ρ1 (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have := (hρ1c.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      rwa [hρ10] at this
    · exact hmain.mono fun δ h => h.2.2.2
  have hT1 := (hPV ζ hζ).comp hρ1w
  have hlin : Tendsto (fun δ : ℝ => 16 * π * M * k * (δ / ‖deriv f ζ‖)) (𝓝[>] 0) (𝓝 0) := by
    have h := (((tendsto_id (x := 𝓝 (0 : ℝ))).div_const ‖deriv f ζ‖).const_mul
      (16 * π * M * k)).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using h
  have hsq : Tendsto (fun δ : ℝ => N * (π * ρ2 δ ^ 2)) (𝓝[>] 0) (𝓝 0) := by
    have h := (((hρ2c.tendsto 0).pow 2).const_mul π).const_mul N
    rw [hρ20] at h
    simpa using h.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hT2 := squeeze_zero_norm' (hmain.mono fun δ h => h.2.1) hlin
  have hT3 := squeeze_zero_norm' (hmain.mono fun δ h => h.2.2.1) hsq
  have hlim := ((hT1.sub hT2).const_mul (1 / π * (deriv f ζ)⁻¹)).sub
    (((tendsto_const_nhds (x := lam * 𝔲 ζ)).sub hT3).const_mul (deriv f ζ)⁻¹)
  have hv : 1 / (π : ℂ) * (deriv f ζ)⁻¹ * (0 - 0) - (deriv f ζ)⁻¹ * (lam * 𝔲 ζ - 0) =
      -lam * (𝔲 ζ * (deriv f ζ)⁻¹) := by ring
  rw [hv] at hlim
  exact hlim.congr' (hmain.mono fun δ h => h.1.symm)

/-- `PV ∬_{𝔻*} \overline{𝔳(η)}/(ζ - η)² d²η = 0` for `𝔳 ∈ A₂¹(𝔻*)`, `ζ ∈ 𝔻*`. -/
theorem e212_pv_zero_ext {𝔳 : ℂ → ℂ} (h𝔳 : 𝔳 ∈ A21fun unitDiscExterior) {ζ : ℂ} (hζ : ζ ∈ unitDiscExterior) :
    Tendsto (fun δ : ℝ => ∫ η in unitDiscExterior \ ball ζ δ, conj (𝔳 η) / (ζ - η) ^ 2) (𝓝[>] 0) (𝓝 0) := by
  have hζ1 : 1 < ‖ζ‖ := hζ
  have hζ0 : ζ ≠ 0 := norm_pos_iff.mp (by linarith)
  -- the inverted form `H ∈ A₂¹(𝔻)`, `H(w) = 𝔳(1/w)·(-1/w²)`
  obtain ⟨H, hH, hHeq, -⟩ :=
    a21_remove_puncture (a21_pullback (isOpen_ball.sdiff isClosed_singleton) a21_inversion_conformal h𝔳)
  have hHw : ∀ w ∈ unitDisc \ {(0 : ℂ)}, H w = 𝔳 w⁻¹ * -(w ^ 2)⁻¹ := by
    intro w hw
    rw [hHeq hw]
    show 𝔳 w⁻¹ * deriv (fun v : ℂ => v⁻¹) w = _
    rw [deriv_inv]
  obtain ⟨z, hzd⟩ : ∃ z : ℂ, z = ζ⁻¹ := ⟨_, rfl⟩
  have hzn : ‖z‖ = ‖ζ‖⁻¹ := by rw [hzd, norm_inv]
  have hz0 : 0 < ‖z‖ := by rw [hzn]; positivity
  have hz1 : ‖z‖ < 1 := by rw [hzn]; exact inv_lt_one_of_one_lt₀ hζ1
  have hzD : z ∈ unitDisc := mem_ball_zero_iff.mpr hz1
  -- `closedBall z r0 ⊆ 𝔻` and the bound `M` of `H` there
  obtain ⟨r0, hr0d⟩ : ∃ r0 : ℝ, r0 = (1 - ‖z‖) / 2 := ⟨_, rfl⟩
  have hr0 : 0 < r0 := by rw [hr0d]; linarith
  have hcl : closedBall z r0 ⊆ unitDisc := by
    intro w hw
    have hd : ‖w - z‖ ≤ r0 := by simpa [mem_closedBall, dist_eq_norm] using hw
    have := norm_le_norm_add_norm_sub' w z
    show w ∈ ball (0 : ℂ) 1
    rw [mem_ball_zero_iff]
    rw [hr0d] at hd
    linarith
  obtain ⟨M0, hM0⟩ := (isCompact_closedBall z r0).exists_bound_of_continuousOn
    (hH.1.continuousOn.mono hcl)
  obtain ⟨M, hMd⟩ : ∃ M : ℝ, M = max M0 0 := ⟨_, rfl⟩
  have hM0' : 0 ≤ M := by rw [hMd]; exact le_max_right _ _
  have hM : ∀ w ∈ closedBall z r0, ‖H w‖ ≤ M := fun w hw =>
    (hM0 w hw).trans (by rw [hMd]; exact le_max_left _ _)
  obtain ⟨G, hG⟩ : ∃ G : ℂ → ℂ, G = fun w => conj (H w) / (z - w) ^ 2 := ⟨_, rfl⟩
  -- the main term: `remark_2_4` at the inner radius `ρ₁(δ) = δ‖z‖²/(1 + δ‖z‖)`
  have hT1 : Tendsto (fun δ : ℝ => ∫ w in unitDisc \ ball z (δ * ‖z‖ ^ 2 / (1 + δ * ‖z‖)), G w)
      (𝓝[>] 0) (𝓝 0) := by
    have hρ : Tendsto (fun δ : ℝ => δ * ‖z‖ ^ 2 / (1 + δ * ‖z‖)) (𝓝[>] 0) (𝓝[>] 0) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have h0 : Tendsto (fun δ : ℝ => δ * ‖z‖ ^ 2 / (1 + δ * ‖z‖)) (𝓝 0)
            (𝓝 (0 * ‖z‖ ^ 2 / (1 + 0 * ‖z‖))) :=
          ((continuous_id.mul continuous_const).tendsto 0).div
            ((continuous_const.add (continuous_id.mul continuous_const)).tendsto 0) (by simp)
        simpa using h0.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with δ hδ
        have hδ' : 0 < δ := hδ
        show 0 < δ * ‖z‖ ^ 2 / (1 + δ * ‖z‖)
        positivity
    rw [hG]
    exact (remark_2_4 hH hzD).comp hρ
  -- smallness of `δ`
  have hsm : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ * ‖z‖ ≤ 1 / 2 ∧ δ * ‖z‖ ^ 2 / (1 - δ * ‖z‖) ≤ r0 ∧ δ ≤ 1 := by
    have h1 : Tendsto (fun δ : ℝ => δ * ‖z‖) (𝓝 0) (𝓝 0) := by
      have := (tendsto_id (x := 𝓝 (0 : ℝ))).mul_const ‖z‖
      simpa using this
    have h2 : Tendsto (fun δ : ℝ => δ * ‖z‖ ^ 2 / (1 - δ * ‖z‖)) (𝓝 0) (𝓝 0) := by
      have := ((tendsto_id (x := 𝓝 (0 : ℝ))).mul_const (‖z‖ ^ 2)).div
        ((tendsto_const_nhds (x := (1 : ℝ))).sub ((tendsto_id (x := 𝓝 (0 : ℝ))).mul_const ‖z‖))
        (by simp)
      simp only [zero_mul, sub_zero, zero_div] at this
      exact this
    exact ((h1.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).and
      ((h2.eventually (ge_mem_nhds hr0)).and (ge_mem_nhds (by norm_num : (0 : ℝ) < 1)))).filter_mono
      nhdsWithin_le_nhds
  -- `J(δ) = -z² (T₁(δ) - T₂(δ))` with `‖T₂(δ)‖ ≤ 16πM‖z‖δ`
  have hmain : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      (∫ η in unitDiscExterior \ ball ζ δ, conj (𝔳 η) / (ζ - η) ^ 2) =
        -z ^ 2 * ((∫ w in unitDisc \ ball z (δ * ‖z‖ ^ 2 / (1 + δ * ‖z‖)), G w) -
          ∫ w in {w : ℂ | ‖w⁻¹ - ζ‖ < δ} \ ball z (δ * ‖z‖ ^ 2 / (1 + δ * ‖z‖)), G w) ∧
      ‖∫ w in {w : ℂ | ‖w⁻¹ - ζ‖ < δ} \ ball z (δ * ‖z‖ ^ 2 / (1 + δ * ‖z‖)), G w‖ ≤
        16 * π * M * ‖z‖ * δ := by
    filter_upwards [hsm, self_mem_nhdsWithin] with δ hδs hδ0
    obtain ⟨hq, hρ2r, hδ1⟩ := hδs
    have hδ : 0 < δ := hδ0
    obtain ⟨q, hqd⟩ : ∃ q : ℝ, q = δ * ‖z‖ := ⟨_, rfl⟩
    rw [← hqd] at hq hρ2r ⊢
    have hq0 : 0 < q := by rw [hqd]; positivity
    have h1q : 0 < 1 - q := by linarith
    obtain ⟨ρ1, hρ1d⟩ : ∃ ρ1 : ℝ, ρ1 = δ * ‖z‖ ^ 2 / (1 + q) := ⟨_, rfl⟩
    obtain ⟨ρ2, hρ2d⟩ : ∃ ρ2 : ℝ, ρ2 = δ * ‖z‖ ^ 2 / (1 - q) := ⟨_, rfl⟩
    rw [← hρ1d]
    rw [← hρ2d] at hρ2r
    have hρ1 : 0 < ρ1 := by rw [hρ1d]; positivity
    have hρ2 : 0 < ρ2 := by rw [hρ2d]; positivity
    have hρ12 : ρ1 ≤ ρ2 := by
      rw [hρ1d, hρ2d]
      apply div_le_div_of_nonneg_left (by positivity) h1q
      linarith
    obtain ⟨E, hEd⟩ : ∃ E : Set ℂ, E = {w : ℂ | ‖w⁻¹ - ζ‖ < δ} := ⟨_, rfl⟩
    rw [← hEd]
    have hEm : MeasurableSet E := by
      rw [hEd]
      exact measurableSet_lt ((measurable_inv.sub_const ζ).norm) measurable_const
    have hmemE : ∀ w, w ∈ E ↔ ‖w⁻¹ - ζ‖ < δ := fun w => by rw [hEd]; rfl
    -- `‖1/w - ζ‖ = ‖z - w‖/(‖w‖‖z‖)`
    have hkey : ∀ w : ℂ, w ≠ 0 → ‖w⁻¹ - ζ‖ = ‖z - w‖ / (‖w‖ * ‖z‖) := by
      intro w hw
      have hz0' : z ≠ 0 := norm_pos_iff.mp hz0
      have hζz : ζ = z⁻¹ := by rw [hzd, inv_inv]
      have : w⁻¹ - ζ = (z - w) / (w * z) := by
        rw [hζz]
        field_simp
      rw [this, norm_div, norm_mul]
    have h0E : (0 : ℂ) ∉ E := by
      intro h
      have h' := (hmemE 0).mp h
      rw [inv_zero, zero_sub, norm_neg] at h'
      linarith
    have hB1E : ball z ρ1 ⊆ E := by
      intro w hw
      have hd : ‖w - z‖ < ρ1 := by simpa [mem_ball, dist_eq_norm] using hw
      have hid1 : δ * ‖z‖ * (‖z‖ - ρ1) = ρ1 := by
        rw [hρ1d, hqd]
        field_simp
        ring
      have hρ1z : ρ1 < ‖z‖ := by
        by_contra hc
        push Not at hc
        have : δ * ‖z‖ * (‖z‖ - ρ1) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
        linarith
      have hw' : ‖z‖ - ρ1 < ‖w‖ := by
        have := norm_le_norm_add_norm_sub' z w
        rw [norm_sub_rev z w] at this
        linarith
      have hw0 : w ≠ 0 := norm_pos_iff.mp (by linarith)
      rw [hmemE, hkey w hw0, div_lt_iff₀ (by positivity), norm_sub_rev]
      calc ‖w - z‖ < ρ1 := hd
        _ = δ * ‖z‖ * (‖z‖ - ρ1) := hid1.symm
        _ ≤ δ * ‖z‖ * ‖w‖ := mul_le_mul_of_nonneg_left hw'.le (by positivity)
        _ = δ * (‖w‖ * ‖z‖) := by ring
    have hEB2 : E ⊆ ball z ρ2 := by
      intro w hw
      have hw0 : w ≠ 0 := fun h => h0E (h ▸ hw)
      have hlt := (hmemE w).mp hw
      rw [hkey w hw0, div_lt_iff₀ (by positivity)] at hlt
      have hwz : ‖w‖ ≤ ‖z‖ + ‖z - w‖ := by
        have := norm_le_norm_add_norm_sub' w z
        rw [norm_sub_rev w z] at this
        linarith
      rw [mem_ball, dist_eq_norm, norm_sub_rev, hρ2d, lt_div_iff₀ h1q]
      have : ‖z - w‖ < δ * (‖w‖ * ‖z‖) := hlt
      rw [hqd]
      have hmul := mul_le_mul_of_nonneg_left hwz (by positivity : (0 : ℝ) ≤ δ * ‖z‖)
      nlinarith [norm_nonneg (z - w), norm_nonneg z]
    have hB2r : ball z ρ2 ⊆ closedBall z r0 := ball_subset_closedBall.trans (closedBall_subset_closedBall hρ2r)
    have hED : E ⊆ unitDisc := fun w hw => hcl (hB2r (hEB2 hw))
    constructor
    · -- change of variables `η = 1/w`
      obtain ⟨S, hSd⟩ : ∃ S : Set ℂ, S = (unitDisc \ {(0 : ℂ)}) \ E := ⟨_, rfl⟩
      have hSm : MeasurableSet S := by
        rw [hSd]
        exact (measurableSet_ball.diff (measurableSet_singleton 0)).diff hEm
      have hS0 : ∀ w ∈ S, w ≠ 0 := fun w hw => by rw [hSd] at hw; exact hw.1.2
      have himg : (fun w : ℂ => w⁻¹) '' S = unitDiscExterior \ ball ζ δ := by
        ext η
        constructor
        · rintro ⟨w, hw, rfl⟩
          rw [hSd] at hw
          obtain ⟨⟨hwD, hw0⟩, hwE⟩ := hw
          have hw0' : w ≠ 0 := hw0
          refine ⟨?_, ?_⟩
          · show 1 < ‖w⁻¹‖
            rw [norm_inv]
            exact (one_lt_inv₀ (norm_pos_iff.mpr hw0')).mpr (mem_ball_zero_iff.mp hwD)
          · intro hb
            apply hwE
            rw [hmemE]
            simpa [mem_ball, dist_eq_norm] using hb
        · rintro ⟨hη, hηb⟩
          have hη1 : 1 < ‖η‖ := hη
          have hη0 : η ≠ 0 := norm_pos_iff.mp (by linarith)
          refine ⟨η⁻¹, ?_, inv_inv η⟩
          rw [hSd]
          refine ⟨⟨?_, ?_⟩, ?_⟩
          · show η⁻¹ ∈ ball (0 : ℂ) 1
            rw [mem_ball_zero_iff, norm_inv]
            exact inv_lt_one_of_one_lt₀ hη1
          · exact inv_ne_zero hη0
          · intro hE
            apply hηb
            have h' := (hmemE _).mp hE
            rw [inv_inv] at h'
            simpa [mem_ball, dist_eq_norm] using h'
      rw [← himg, e212_cov_inv hSm hS0]
      have hcongr : ∀ w ∈ S, ((‖-(w ^ 2)⁻¹‖ ^ 2 : ℝ) : ℂ) * (conj (𝔳 w⁻¹) / (ζ - w⁻¹) ^ 2) =
          -z ^ 2 * G w := by
        intro w hw
        have hw' : w ∈ unitDisc \ {(0 : ℂ)} := by rw [hSd] at hw; exact hw.1
        rw [e212_inv_integrand (hS0 w hw) hζ0, hG]
        dsimp only
        rw [hHw w hw', hzd]
      rw [setIntegral_congr_fun hSm hcongr, integral_const_mul]
      congr 1
      have hSeq : S = (unitDisc \ E) \ {(0 : ℂ)} := by rw [hSd, Set.sdiff_sdiff_comm]
      rw [hSeq, setIntegral_congr_set (sdiff_null_ae_eq_self (measure_singleton (0 : ℂ)))]
      have hsplit : unitDisc \ E = (unitDisc \ ball z ρ1) \ (E \ ball z ρ1) := by
        ext w
        simp only [Set.mem_sdiff]
        constructor
        · rintro ⟨hwD, hwE⟩
          exact ⟨⟨hwD, fun h => hwE (hB1E h)⟩, fun h => hwE h.1⟩
        · rintro ⟨⟨hwD, hwB⟩, hw⟩
          exact ⟨hwD, fun h => hw ⟨h, hwB⟩⟩
      have hGi : IntegrableOn G (unitDisc \ ball z ρ1) := by
        rw [hG]
        exact remark_2_4_truncated_integrable hH z hρ1
      rw [hsplit, setIntegral_sdiff (hEm.diff measurableSet_ball) hGi (fun w hw => ⟨hED hw.1, hw.2⟩)]
    · -- the crescent bound
      have hT : E \ ball z ρ1 ⊆ ball z ρ2 \ ball z ρ1 := fun w hw => ⟨hEB2 hw.1, hw.2⟩
      have hbd : ∀ w ∈ E \ ball z ρ1, ‖G w‖ ≤ M / ρ1 ^ 2 := by
        intro w hw
        obtain ⟨hw2, hw1⟩ := hT hw
        have hd1 : ρ1 ≤ ‖z - w‖ := by
          rw [norm_sub_rev]
          simpa [mem_ball, dist_eq_norm] using hw1
        have hwc : w ∈ closedBall z r0 := hB2r hw2
        rw [hG]
        dsimp only
        rw [norm_div, Complex.norm_conj, norm_pow]
        have hzw : 0 < ‖z - w‖ ^ 2 := by have := hρ1.trans_le hd1; positivity
        rw [div_le_div_iff₀ hzw (by positivity)]
        calc ‖H w‖ * ρ1 ^ 2 ≤ M * ρ1 ^ 2 := mul_le_mul_of_nonneg_right (hM w hwc) (by positivity)
          _ ≤ M * ‖z - w‖ ^ 2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ1.le hd1 2) hM0'
      have hvb : ∀ r : ℝ, 0 ≤ r → volume (ball z r) = ENNReal.ofReal (π * r ^ 2) := by
        intro r hr
        rw [Complex.volume_ball, ENNReal.ofReal_mul Real.pi_pos.le, ENNReal.ofReal_pow hr,
          ← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
        exact mul_comm _ _
      have hvolT : volume (E \ ball z ρ1) ≤ ENNReal.ofReal (π * ρ2 ^ 2 - π * ρ1 ^ 2) := by
        calc volume (E \ ball z ρ1) ≤ volume (ball z ρ2 \ ball z ρ1) := measure_mono hT
          _ = volume (ball z ρ2) - volume (ball z ρ1) :=
              measure_sdiff (ball_subset_ball hρ12) measurableSet_ball.nullMeasurableSet
                measure_ball_lt_top.ne
          _ = ENNReal.ofReal (π * ρ2 ^ 2 - π * ρ1 ^ 2) := by
              rw [hvb ρ2 hρ2.le, hvb ρ1 hρ1.le, ENNReal.ofReal_sub _ (by positivity)]
      have hTfin : volume (E \ ball z ρ1) < ∞ := lt_of_le_of_lt hvolT ENNReal.ofReal_lt_top
      have hvr : (volume (E \ ball z ρ1)).toReal ≤ π * ρ2 ^ 2 - π * ρ1 ^ 2 :=
        ENNReal.toReal_le_of_le_ofReal
          (sub_nonneg.mpr (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ1.le hρ12 2) Real.pi_pos.le)) hvolT
      have hint := norm_setIntegral_le_of_norm_le_const hTfin hbd
      have hratio : M / ρ1 ^ 2 * (π * ρ2 ^ 2 - π * ρ1 ^ 2) = π * M * (4 * q / (1 - q) ^ 2) := by
        rw [hρ1d, hρ2d]
        have h1 : (1 + q) ≠ 0 := by linarith
        have h2 : (1 - q) ≠ 0 := by linarith
        have h3 : δ * ‖z‖ ^ 2 ≠ 0 := by positivity
        field_simp
        ring
      calc ‖∫ w in E \ ball z ρ1, G w‖ ≤ M / ρ1 ^ 2 * (volume (E \ ball z ρ1)).toReal := hint
        _ ≤ M / ρ1 ^ 2 * (π * ρ2 ^ 2 - π * ρ1 ^ 2) :=
            mul_le_mul_of_nonneg_left hvr (by positivity)
        _ = π * M * (4 * q / (1 - q) ^ 2) := hratio
        _ ≤ π * M * (16 * q) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            rw [div_le_iff₀ (by positivity)]
            have h4 : (1 / 4 : ℝ) ≤ (1 - q) ^ 2 := by nlinarith
            nlinarith [mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ 16 * q)]
        _ = 16 * π * M * ‖z‖ * δ := by rw [hqd]; ring
  -- conclude
  have hlin : Tendsto (fun δ : ℝ => 16 * π * M * ‖z‖ * δ) (𝓝[>] 0) (𝓝 0) := by
    have h := ((tendsto_id (x := 𝓝 (0 : ℝ))).const_mul (16 * π * M * ‖z‖)).mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using h
  have hT2 : Tendsto (fun δ : ℝ =>
      ∫ w in {w : ℂ | ‖w⁻¹ - ζ‖ < δ} \ ball z (δ * ‖z‖ ^ 2 / (1 + δ * ‖z‖)), G w) (𝓝[>] 0) (𝓝 0) :=
    squeeze_zero_norm' (hmain.mono fun δ h => h.2) hlin
  have hlim := (hT1.sub hT2).const_mul (-z ^ 2)
  rw [sub_zero, mul_zero] at hlim
  exact hlim.congr' (hmain.mono fun δ h => h.1.symm)

/-- Transport of a `K₁`-eigenform to `Ω = f(𝔻)`: with `u = (𝔲 ∘ f⁻¹)(f⁻¹)'`,
`PV (1/π) ∬_Ω \overline{u(w)}/(z - w)² d²w = -λ u(z)` (Euclidean excision in `Ω`). -/
theorem e212_pv_disc {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc (f '' unitDisc)) {𝔲 : ℂ → ℂ}
    (h𝔲 : 𝔲 ∈ A21fun unitDisc) {lam : ℂ}
    (hK : ∀ ζ ∈ unitDisc, (∫ w in unitDisc, kerK1 f ζ w * conj (𝔲 w)) = lam * 𝔲 ζ) :
    ∀ z ∈ f '' unitDisc, Tendsto (fun δ : ℝ => 1 / π * ∫ w in f '' unitDisc \ ball z δ,
        conj (𝔲 (Function.invFunOn f unitDisc w) * deriv (Function.invFunOn f unitDisc) w) / (z - w) ^ 2)
      (𝓝[>] 0) (𝓝 (-lam * (𝔲 (Function.invFunOn f unitDisc z) * deriv (Function.invFunOn f unitDisc) z))) := by
  exact e212_pv_gen isOpen_ball hf h𝔲 hK (fun _ hζ => remark_2_4 h𝔲 hζ)

/-- Transport of a `K₄`-eigenform to `Ω* = g(𝔻*)`. -/
theorem e212_pv_ext {g : ℂ → ℂ} (hg : IsConformalOnto g unitDiscExterior (g '' unitDiscExterior)) {𝔳 : ℂ → ℂ}
    (h𝔳 : 𝔳 ∈ A21fun unitDiscExterior) {lam : ℂ}
    (hK : ∀ ζ ∈ unitDiscExterior, (∫ w in unitDiscExterior, kerK4 g ζ w * conj (𝔳 w)) = lam * 𝔳 ζ) :
    ∀ z ∈ g '' unitDiscExterior, Tendsto (fun δ : ℝ => 1 / π * ∫ w in g '' unitDiscExterior \ ball z δ,
        conj (𝔳 (Function.invFunOn g unitDiscExterior w) * deriv (Function.invFunOn g unitDiscExterior) w) /
          (z - w) ^ 2)
      (𝓝[>] 0)
      (𝓝 (-lam * (𝔳 (Function.invFunOn g unitDiscExterior z) * deriv (Function.invFunOn g unitDiscExterior) z))) := by
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  refine e212_pv_gen hEo hg h𝔳 (fun ζ hζ => ?_) (fun _ hζ => e212_pv_zero_ext h𝔳 hζ)
  have he : (fun w => kerK1 g ζ w * conj (𝔳 w)) = fun w => kerK4 g ζ w * conj (𝔳 w) := rfl
  rw [he]
  exact hK ζ hζ

/-- Cross identity on `Ω*` from `K₃` (no principal value: `z ∉ \bar Ω`). -/
theorem e212_cross_disc {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g) {𝔲 𝔳 : ℂ → ℂ}
    (h𝔲 : 𝔲 ∈ A21fun unitDisc) {c : ℂ}
    (hK : ∀ ζ ∈ unitDiscExterior, (∫ w in unitDisc, kerK3 f g ζ w * conj (𝔲 w)) = c * 𝔳 ζ) :
    ∀ z ∈ g '' unitDiscExterior, 1 / π * (∫ w in f '' unitDisc,
        conj (𝔲 (Function.invFunOn f unitDisc w) * deriv (Function.invFunOn f unitDisc) w) / (z - w) ^ 2) =
      c * (𝔳 (Function.invFunOn g unitDiscExterior z) * deriv (Function.invFunOn g unitDiscExterior) z) := by
  -- `h𝔲` is not needed: the identity is a pointwise change of variables.
  have _h := h𝔲
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  refine e212_cross_gen isOpen_ball hEo ⟨h.1, h.2.1, rfl⟩ ⟨h.2.2.2.2.1.1, h.2.2.2.2.1.2.1, rfl⟩
    (fun ζ hζ η hη he => h.2.2.2.2.2.ne_of_mem ⟨η, hη, rfl⟩ ⟨ζ, hζ, rfl⟩ he.symm)
    (fun ζ _ η _ => rfl) hK

/-- Cross identity on `Ω` from `K₂`. -/
theorem e212_cross_ext {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g) {𝔲 𝔳 : ℂ → ℂ}
    (h𝔳 : 𝔳 ∈ A21fun unitDiscExterior) {c : ℂ}
    (hK : ∀ ζ ∈ unitDisc, (∫ w in unitDiscExterior, kerK2 f g ζ w * conj (𝔳 w)) = c * 𝔲 ζ) :
    ∀ z ∈ f '' unitDisc, 1 / π * (∫ w in g '' unitDiscExterior,
        conj (𝔳 (Function.invFunOn g unitDiscExterior w) * deriv (Function.invFunOn g unitDiscExterior) w) /
          (z - w) ^ 2) =
      c * (𝔲 (Function.invFunOn f unitDisc z) * deriv (Function.invFunOn f unitDisc) z) := by
  -- `h𝔳` is not needed: the identity is a pointwise change of variables.
  have _h := h𝔳
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  refine e212_cross_gen hEo isOpen_ball ⟨h.2.2.2.2.1.1, h.2.2.2.2.1.2.1, rfl⟩ ⟨h.1, h.2.1, rfl⟩
    (fun ζ hζ η hη he => h.2.2.2.2.2.ne_of_mem ⟨ζ, hζ, rfl⟩ ⟨η, hη, rfl⟩ he)
    (fun ζ _ η _ => rfl) hK

/-- Conformal invariance of the pairing of 1-forms: `∬_{F(D)} (a∘F⁻¹)(F⁻¹)' \overline{(b∘F⁻¹)(F⁻¹)'} = ∬_D a \bar b`. -/
theorem e212_ortho {F : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D) (hF : IsConformalOnto F D (F '' D)) {a b : ℂ → ℂ}
    (ha : a ∈ A21fun D) (hb : b ∈ A21fun D) :
    (∫ w in F '' D, a (Function.invFunOn F D w) * deriv (Function.invFunOn F D) w *
        conj (b (Function.invFunOn F D w) * deriv (Function.invFunOn F D) w)) = ∫ z in D, a z * conj (b z) := by
  -- `ha`, `hb` are not needed: the change of variables holds for any integrands.
  have _ha := ha
  have _hb := hb
  rw [faber_a21_pairing_pullback hD hF.1 hF.2.1]
  refine setIntegral_congr_fun hD.measurableSet fun z hz => ?_
  have hl : Function.invFunOn F D (F z) = z := hF.2.1.leftInvOn_invFunOn hz
  have hd := t1_deriv_invFunOn_mul hD hF hz
  show a (Function.invFunOn F D (F z)) * deriv (Function.invFunOn F D) (F z) * deriv F z *
      conj (b (Function.invFunOn F D (F z)) * deriv (Function.invFunOn F D) (F z) * deriv F z) = _
  rw [hl, mul_assoc (a z), hd, mul_one, mul_assoc (b z), hd, mul_one]

/-- The transported form `(a ∘ F⁻¹)(F⁻¹)'` is holomorphic on `F(D)`. -/
theorem e212_form_diff {F : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D) (hF : IsConformalOnto F D (F '' D)) {a : ℂ → ℂ}
    (ha : DifferentiableOn ℂ a D) :
    DifferentiableOn ℂ (fun w => a (Function.invFunOn F D w) * deriv (Function.invFunOn F D) w) (F '' D) := by
  obtain ⟨hopen, hinv⟩ := RMT.differentiableOn_invFunOn_of_injOn hD hF.1 hF.2.1
  have hmaps : MapsTo (Function.invFunOn F D) (F '' D) D := by
    rintro w ⟨z, hz, rfl⟩
    exact Function.invFunOn_mem ⟨z, hz, rfl⟩
  exact (ha.comp hinv hmaps).mul (hinv.deriv hopen)

/-! ### (2.12) -/


/-- **(2.12)** (TT:4384–4464). Let `[μ] ∈ T₀(1)`, `Ω = 𝖿(𝔻)`, `Ω* = 𝗀(𝔻*)`. There are `λ_n ∈ [0, 1)`, the singular
values of `B₁`, and holomorphic 1-forms `u_n` on `Ω`, `v_n` on `Ω*` (orthonormal bases of `A₂¹(Ω)`, `A₂¹(Ω*)`), with
`ρ_n = √(1 - λ_n²)`, such that for `z ∈ Ω` resp. `z ∈ Ω*`:
- `(1/π) ∬_Ω \overline{u_n(w)}/(z - w)² d²w = -λ_n u_n(z)` on `Ω`, and `= ρ_n v_n(z)` on `Ω*`;
- `(1/π) ∬_{Ω*} \overline{v_n(w)}/(z - w)² d²w = ρ_n u_n(z)` on `Ω`, and `= λ_n v_n(z)` on `Ω*`.

(The integrals over the domain containing `z` are principal values.) -/
theorem e212_eq_2_12 {p : T1} (hp : p ∈ T01) :
    let μ : LinfStar := (Quotient.out p : LinfStarBall)
    let Ω := fsans μ '' unitDisc
    let Ωs := gsans μ '' unitDiscExterior
    ∃ lam : ℕ → ℝ, IsSingularSeq (B1 (grunsky (fsans μ) (gsans μ))) lam ∧ (∀ n, lam n < 1) ∧
      ∃ u v : ℕ → ℂ → ℂ, (∀ n, DifferentiableOn ℂ (u n) Ω ∧ DifferentiableOn ℂ (v n) Ωs) ∧
        (∀ m n, (∫ z in Ω, u m z * conj (u n z)) = kron m n ∧ (∫ z in Ωs, v m z * conj (v n z)) = kron m n) ∧
        ∀ n, (∀ z ∈ Ω, Tendsto (fun δ : ℝ => 1 / π * ∫ w in Ω \ ball z δ, conj (u n w) / (z - w) ^ 2) (𝓝[>] 0)
              (𝓝 (-(lam n : ℂ) * u n z))) ∧
          (∀ z ∈ Ωs, 1 / π * ∫ w in Ω, conj (u n w) / (z - w) ^ 2 = Real.sqrt (1 - lam n ^ 2) * v n z) ∧
          (∀ z ∈ Ω, 1 / π * ∫ w in Ωs, conj (v n w) / (z - w) ^ 2 = Real.sqrt (1 - lam n ^ 2) * u n z) ∧
          (∀ z ∈ Ωs, Tendsto (fun δ : ℝ => 1 / π * ∫ w in Ωs \ ball z δ, conj (v n w) / (z - w) ^ 2) (𝓝[>] 0)
              (𝓝 ((lam n : ℂ) * v n z))) := by
  intro μ Ω Ωs
  have hμ : μ ∈ LinfStarBall := (Quotient.out p : LinfStarBall).2
  have hpair := AppB.b8_welding_normalized_pair hμ
  have hF := r22_complement_null hμ
  have hHS := ((cor_2_9 p).1).mp hp
  obtain ⟨U, d, hd, hrow, hcol, hBU⟩ := e212_takagi hμ hHS
  have hlt := e212_lam_lt hμ hcol hBU
  obtain ⟨V, hcolV, h2, h3, h4⟩ := e212_V hμ hd hrow hcol hBU hlt
  obtain ⟨h𝔲, h𝔳, ho𝔲, ho𝔳⟩ := e212_forms hcol hcolV
  have hcf := S2C.s2c_conf_f hμ
  have hcg := S2C.s2c_conf_g hμ
  have hDo : IsOpen unitDisc := isOpen_ball
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  refine ⟨d, e212_singular hμ hHS hd hrow hcol hBU, hlt,
    fun n w => (∑' m, U m n * basisE m (Function.invFunOn (fsans μ) unitDisc w)) *
      deriv (Function.invFunOn (fsans μ) unitDisc) w,
    fun n w => (∑' m, conj (V m n) * basisF m (Function.invFunOn (gsans μ) unitDiscExterior w)) *
      deriv (Function.invFunOn (gsans μ) unitDiscExterior) w, ?_, ?_, ?_⟩
  · intro n
    exact ⟨e212_form_diff hDo hcf (h𝔲 n).1, e212_form_diff hEo hcg (h𝔳 n).1⟩
  · intro m n
    exact ⟨(e212_ortho hDo hcf (h𝔲 m) (h𝔲 n)).trans (ho𝔲 m n),
      (e212_ortho hEo hcg (h𝔳 m) (h𝔳 n)).trans (ho𝔳 m n)⟩
  · intro n
    obtain ⟨k1, k3, k2, k4⟩ := e212_kernel hpair hF hcol hcolV hBU h2 h3 h4 n
    refine ⟨e212_pv_disc hcf (h𝔲 n) k1, e212_cross_disc hpair (h𝔲 n) k3,
      e212_cross_ext hpair (h𝔳 n) k2, ?_⟩
    intro z hz
    have := e212_pv_ext hcg (h𝔳 n) k4 z hz
    simpa only [neg_neg] using this

/-- **(2.12)** (TT:4384–4464). Let `[μ] ∈ T₀(1)`, `Ω = 𝖿(𝔻)`, `Ω* = 𝗀(𝔻*)`. There are `λ_n ∈ [0, 1)`, the singular
values of `B₁`, and holomorphic 1-forms `u_n` on `Ω`, `v_n` on `Ω*` (orthonormal bases of `A₂¹(Ω)`, `A₂¹(Ω*)`), with
`ρ_n = √(1 - λ_n²)`, such that for `z ∈ Ω` resp. `z ∈ Ω*`:
- `(1/π) ∬_Ω \overline{u_n(w)}/(z - w)² d²w = -λ_n u_n(z)` on `Ω`, and `= ρ_n v_n(z)` on `Ω*`;
- `(1/π) ∬_{Ω*} \overline{v_n(w)}/(z - w)² d²w = ρ_n u_n(z)` on `Ω`, and `= λ_n v_n(z)` on `Ω*`.

(The integrals over the domain containing `z` are principal values.) -/
theorem eq_2_12 {p : T1} (hp : p ∈ T01) :
    let μ : LinfStar := (Quotient.out p : LinfStarBall)
    let Ω := fsans μ '' unitDisc
    let Ωs := gsans μ '' unitDiscExterior
    ∃ lam : ℕ → ℝ, IsSingularSeq (B1 (grunsky (fsans μ) (gsans μ))) lam ∧ (∀ n, lam n < 1) ∧
      ∃ u v : ℕ → ℂ → ℂ, (∀ n, DifferentiableOn ℂ (u n) Ω ∧ DifferentiableOn ℂ (v n) Ωs) ∧
        (∀ m n, (∫ z in Ω, u m z * conj (u n z)) = kron m n ∧ (∫ z in Ωs, v m z * conj (v n z)) = kron m n) ∧
        ∀ n, (∀ z ∈ Ω, Tendsto (fun δ : ℝ => 1 / π * ∫ w in Ω \ ball z δ, conj (u n w) / (z - w) ^ 2) (𝓝[>] 0)
              (𝓝 (-(lam n : ℂ) * u n z))) ∧
          (∀ z ∈ Ωs, 1 / π * ∫ w in Ω, conj (u n w) / (z - w) ^ 2 = Real.sqrt (1 - lam n ^ 2) * v n z) ∧
          (∀ z ∈ Ω, 1 / π * ∫ w in Ωs, conj (v n w) / (z - w) ^ 2 = Real.sqrt (1 - lam n ^ 2) * u n z) ∧
          (∀ z ∈ Ωs, Tendsto (fun δ : ℝ => 1 / π * ∫ w in Ωs \ ball z δ, conj (v n w) / (z - w) ^ 2) (𝓝[>] 0)
              (𝓝 ((lam n : ℂ) * v n z))) :=
  e212_eq_2_12 hp

end Ch2
end TakhtajanTeo
