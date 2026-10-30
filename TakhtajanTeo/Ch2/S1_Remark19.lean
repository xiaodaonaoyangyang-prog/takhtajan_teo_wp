import TakhtajanTeo.Ch2.S1_Part3
import TakhtajanTeo.Ch1.Eq19Completed
import TakhtajanTeo.Ch1.CircleQCPlaneExtension
import TakhtajanTeo.Ch1.CuiBound
import TakhtajanTeo.Ch1.HilbertManifoldCompleted
import TakhtajanTeo.Appendix.SymmetricBoundaryExtension

/-!
# Remark 1.9, clause 2 — `C³` boundary maps give `T₀(1)`

Host: new module `Ch2/S1_Remark19.lean`, prefix `r19_`.

Route (corrected from the radial-average proposal: `r·exp(i·avg u)` has `μ → (1 - u')/(1 + u') ≠ 0` at `S¹`, so it is
not asymptotically conformal; the `r = 2` Beurling–Ahlfors extension is, with `|μ(x+iy)| = O(y)` for `C²` lifts):
1. `r19_lift`: the `1`-periodic lift `v(x) = u(2πx)/(2π) - k` of `h = w_μ|S¹` is a `GardinerLakic2000.IsCircleLift`,
   `C²`, `v' ≥ m > 0`, quasisymmetric.
2. `r19_ba2_bound`: `|μ_{BA₂ v}(z)| ≤ C Im z` on `ℍ` (`∂̄BA₂ = O(y)` by the mean value theorem on `v'`,
   `|∂BA₂| ≥ m`).
3. `r19_disk_ext`: the `r = 2` analogue of the pieces of `circle_quasisymmetric_plane_extension`
   (`periodicDiskMap (beurlingAhlfors v 2)` is a `K`-qc self-map of `𝔻` fixing `0`, extending `h`).
4. `r19_disk_dilatation`: `|μ_G(w)| ≤ C (-log|w|)/(2π)` a.e. on `𝔻` (`complexDilatation_comp_conformal_left/right`
   through `diskCover`).
5. `r19_L2`: `|ν| ≤ C log|z|` a.e. on `𝔻*` and `‖ν‖∞ < 1` give `‖ν‖_{L²(ρ)} < ∞`.
6. `r19_exists_mu`: `eq19_exists_mu` with the extra conclusion `μ = μ_e` a.e. on `𝔻*` (copy of its body).
7. Assembly: `ab_reflect` keeps `|μ_e(z)| = |μ_G(1/z̄)|` a.e. on `𝔻*`; then `cui_A2_bound` and `cor_3_2`.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC
namespace Ch2

/-- A `C¹` lift with derivative in `[m, M]`, `0 < m`, is `M/m`-quasisymmetric. -/
theorem r19_qs_of_deriv {v : ℝ → ℝ} (hv : ContDiff ℝ 1 v) {m M : ℝ} (hm : 0 < m)
    (hb : ∀ x, m ≤ deriv v x ∧ deriv v x ≤ M) : IsQuasisymmetric v (M / m) := by
  have hd : Differentiable ℝ v := hv.differentiable one_ne_zero
  have hmM : m ≤ M := (hb 0).1.trans (hb 0).2
  have hM : 0 < M := lt_of_lt_of_le hm hmM
  have hsm : StrictMono v := strictMono_of_deriv_pos (fun x => lt_of_lt_of_le hm (hb x).1)
  have hlow : ∀ x, 0 < x → v 0 + m * x ≤ v x := by
    intro x hx; have := (GardinerLakic2000.gl16_incr hv hb hx).1; linarith
  have hup : ∀ x, x < 0 → v x ≤ v 0 + m * x := by
    intro x hx; have := (GardinerLakic2000.gl16_incr hv hb hx).1; linarith
  refine ⟨hsm, hd.continuous, ?_, ?_, fun x t ht => ?_⟩
  · refine tendsto_atTop_mono' atTop ?_ (tendsto_atTop_add_const_left atTop (v 0)
      ((tendsto_id).const_mul_atTop hm))
    filter_upwards [eventually_gt_atTop 0] with x hx
    exact hlow x hx
  · refine tendsto_atBot_mono' atBot ?_ (tendsto_atBot_add_const_left atBot (v 0)
      ((tendsto_id).const_mul_atBot hm))
    filter_upwards [eventually_lt_atBot 0] with x hx
    exact hup x hx
  · obtain ⟨n1, n2⟩ := GardinerLakic2000.gl16_incr hv hb (show x < x + t by linarith)
    obtain ⟨d1, d2⟩ := GardinerLakic2000.gl16_incr hv hb (show x - t < x by linarith)
    simp only [add_sub_cancel_left, sub_sub_cancel] at n1 n2 d1 d2
    have hden : 0 < v x - v (x - t) := by nlinarith
    unfold qsRatio
    constructor
    · rw [inv_div, div_le_div_iff₀ hM hden]; nlinarith
    · rw [div_le_div_iff₀ hden hm]; nlinarith

/-- (1) The normalized `1`-periodic lift of a `C³` circle diffeomorphism `e^{it} ↦ e^{iu(t)}`. -/
theorem r19_lift {h : ℂ → ℂ} {u : ℝ → ℝ} (hu : ContDiff ℝ 3 u) (hpos : ∀ t, 0 < deriv u t)
    (hper : ∀ t, u (t + 2 * π) = u t + 2 * π) (hh : ∀ t : ℝ, h (exp (t * I)) = exp (u t * I)) :
    ∃ v : ℝ → ℝ, GardinerLakic2000.IsCircleLift h v ∧ ContDiff ℝ 2 v ∧
      (∃ m > 0, ∀ x, m ≤ deriv v x) ∧ ∃ ρ, IsQuasisymmetric v ρ := by
  have hπ : (0 : ℝ) < 2 * π := by positivity
  set k : ℤ := ⌊u 0 / (2 * π)⌋
  let v : ℝ → ℝ := fun x => u (2 * π * x) / (2 * π) - k
  have hud : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hvd : ∀ x, HasDerivAt v (deriv u (2 * π * x)) x := by
    intro x
    have h1 := ((hud (2 * π * x)).hasDerivAt.comp x ((hasDerivAt_id x).const_mul (2 * π))).div_const (2 * π)
    have h2 := h1.sub_const (k : ℝ)
    refine h2.congr_deriv ?_
    field_simp
  have hderiv : ∀ x, deriv v x = deriv u (2 * π * x) := fun x => (hvd x).deriv
  have hv2 : ContDiff ℝ 2 v :=
    ((hu.of_le (by norm_num)).comp (contDiff_const.mul contDiff_id)).div_const _ |>.sub contDiff_const
  have hvper : ∀ x, v (x + 1) = v x + 1 := by
    intro x
    simp only [v]
    rw [show 2 * π * (x + 1) = 2 * π * x + 2 * π by ring, hper]
    field_simp
    ring
  have hvpos : ∀ x, 0 < deriv v x := fun x => by rw [hderiv]; exact hpos _
  obtain ⟨m, M, hm, hb⟩ := GardinerLakic2000.gl16_deriv_bounds (hv2.of_le (by norm_num)) hvpos hvper
  have hv0 : v 0 = Int.fract (u 0 / (2 * π)) := by
    simp only [v, mul_zero, Int.fract, k]
  refine ⟨v, ⟨hv2.continuous, strictMono_of_deriv_pos hvpos, ?_, ?_, hvper, fun x => ?_⟩, hv2,
    ⟨m, hm, fun x => (hb x).1⟩, M / m, r19_qs_of_deriv (hv2.of_le (by norm_num)) hm hb⟩
  · rw [hv0]; exact Int.fract_nonneg _
  · rw [hv0]; exact Int.fract_lt_one _
  · have e1 : exp (2 * π * I * x) = exp (((2 * π * x : ℝ) : ℂ) * I) := by push_cast; ring_nf
    rw [e1, hh]
    have e2 : 2 * (π : ℂ) * I * ((v x : ℝ) : ℂ) = ((u (2 * π * x) : ℝ) : ℂ) * I - (k : ℂ) * (2 * π * I) := by
      simp only [v]
      push_cast
      field_simp
    rw [e2, Complex.exp_sub, Complex.exp_int_mul_two_pi_mul_I, div_one]

/-- Mean value bound from `0`: `g 0 = 0` and `|g'| ≤ B` on `[0, y]` give `|g y| ≤ B y`. -/
theorem r19_mvt0 {g g' : ℝ → ℝ} {y B : ℝ} (hy : 0 ≤ y) (hg : ∀ s, HasDerivAt g (g' s) s)
    (hb : ∀ s ∈ Icc 0 y, |g' s| ≤ B) (h0 : g 0 = 0) : |g y| ≤ B * y := by
  have h := norm_image_sub_le_of_norm_deriv_le_segment' (f := g) (a := 0) (b := y)
    (fun s _ => (hg s).hasDerivWithinAt) (fun s hs => by rw [Real.norm_eq_abs]; exact hb s (Ico_subset_Icc_self hs))
    y ⟨hy, le_rfl⟩
  simpa [h0, Real.norm_eq_abs] using h

theorem r19_hasDerivAt_add {f f' : ℝ → ℝ} (hf : ∀ s, HasDerivAt f (f' s) s) (x s : ℝ) :
    HasDerivAt (fun σ => f (x + σ)) (f' (x + s)) s := by
  exact (hf (x + s)).comp_const_add x s

theorem r19_hasDerivAt_sub {f f' : ℝ → ℝ} (hf : ∀ s, HasDerivAt f (f' s) s) (x s : ℝ) :
    HasDerivAt (fun σ => f (x - σ)) (-f' (x - s)) s := by
  exact (hf (x - s)).comp_const_sub x s

/-- The second-difference estimates for a lift with `|v''| ≤ M`, with `P = ∫₀ v`. -/
theorem r19_second_diff {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) {M : ℝ}
    (hM : ∀ s, |deriv (deriv v) s| ≤ M) (x : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    |v (x + y) - v (x - y) - 2 * y * deriv v x| ≤ 2 * M * y ^ 2 ∧
      |v (x + y) - 2 * v x + v (x - y)| ≤ 2 * M * y ^ 2 ∧
      |ba_f1h_prim v (x + y) - 2 * ba_f1h_prim v x + ba_f1h_prim v (x - y) - y ^ 2 * deriv v x| ≤ 2 * M * y ^ 3 ∧
      |ba_f1h_prim v (x + y) - ba_f1h_prim v (x - y) - 2 * y * v x| ≤ 2 * M * y ^ 3 := by
  obtain ⟨hd1, -, hv1⟩ := contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) v from hv)
  obtain ⟨hd2, -, -⟩ := contDiff_succ_iff_deriv.mp (show ContDiff ℝ (0 + 1) (deriv v) from hv1)
  have hvd : ∀ s, HasDerivAt v (deriv v s) s := fun s => (hd1 s).hasDerivAt
  have hv'd : ∀ s, HasDerivAt (deriv v) (deriv (deriv v) s) s := fun s => (hd2 s).hasDerivAt
  have hPd : ∀ s, HasDerivAt (ba_f1h_prim v) (v s) s := ba_f1h_prim_hasDerivAt hd1.continuous
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  -- `|v'(x ± s) - v'(x)| ≤ M s`
  have hLp : ∀ s, 0 ≤ s → |deriv v (x + s) - deriv v x| ≤ M * s := by
    intro s hs
    refine r19_mvt0 (g := fun σ => deriv v (x + σ) - deriv v x) hs
      (fun σ => (r19_hasDerivAt_add hv'd x σ).sub_const _) (fun σ _ => hM _) (by simp)
  have hLm : ∀ s, 0 ≤ s → |deriv v (x - s) - deriv v x| ≤ M * s := by
    intro s hs
    refine r19_mvt0 (g := fun σ => deriv v (x - σ) - deriv v x) hs
      (fun σ => (r19_hasDerivAt_sub hv'd x σ).sub_const _) (fun σ _ => by rw [abs_neg]; exact hM _) (by simp)
  -- `φ(s) = v(x+s) - v(x-s) - 2 s v'(x)`
  have hφ : ∀ s, 0 ≤ s → |v (x + s) - v (x - s) - 2 * s * deriv v x| ≤ 2 * M * s ^ 2 := by
    intro s hs
    have h := r19_mvt0 (g := fun σ => v (x + σ) - v (x - σ) - 2 * σ * deriv v x)
      (g' := fun σ => deriv v (x + σ) + deriv v (x - σ) - 2 * deriv v x) (B := 2 * M * s) hs
      (fun σ => by
        have := ((r19_hasDerivAt_add hvd x σ).sub (r19_hasDerivAt_sub hvd x σ)).sub
          (((hasDerivAt_id σ).const_mul 2).mul_const (deriv v x))
        exact this.congr_deriv (by simp))
      (fun σ hσ => by
        have e : deriv v (x + σ) + deriv v (x - σ) - 2 * deriv v x =
            (deriv v (x + σ) - deriv v x) + (deriv v (x - σ) - deriv v x) := by ring
        rw [e]
        calc _ ≤ |deriv v (x + σ) - deriv v x| + |deriv v (x - σ) - deriv v x| := abs_add_le _ _
          _ ≤ M * σ + M * σ := add_le_add (hLp σ hσ.1) (hLm σ hσ.1)
          _ ≤ 2 * M * s := by nlinarith [hσ.2])
      (by simp)
    calc _ ≤ 2 * M * s * s := h
      _ = 2 * M * s ^ 2 := by ring
  -- `ψ(s) = v(x+s) - 2v(x) + v(x-s)`
  have hψ : ∀ s, 0 ≤ s → |v (x + s) - 2 * v x + v (x - s)| ≤ 2 * M * s ^ 2 := by
    intro s hs
    have h := r19_mvt0 (g := fun σ => v (x + σ) - 2 * v x + v (x - σ))
      (g' := fun σ => deriv v (x + σ) - deriv v (x - σ)) (B := 2 * M * s) hs
      (fun σ => by
        have := ((r19_hasDerivAt_add hvd x σ).sub_const (2 * v x)).add (r19_hasDerivAt_sub hvd x σ)
        exact this.congr_deriv (by ring))
      (fun σ hσ => by
        have e : deriv v (x + σ) - deriv v (x - σ) =
            (deriv v (x + σ) - deriv v x) - (deriv v (x - σ) - deriv v x) := by ring
        rw [e]
        calc _ ≤ |deriv v (x + σ) - deriv v x| + |deriv v (x - σ) - deriv v x| := abs_sub _ _
          _ ≤ M * σ + M * σ := add_le_add (hLp σ hσ.1) (hLm σ hσ.1)
          _ ≤ 2 * M * s := by nlinarith [hσ.2])
      (by simp; ring)
    calc _ ≤ 2 * M * s * s := h
      _ = 2 * M * s ^ 2 := by ring
  refine ⟨hφ y hy, hψ y hy, ?_, ?_⟩
  · have h := r19_mvt0 (g := fun σ => ba_f1h_prim v (x + σ) - 2 * ba_f1h_prim v x + ba_f1h_prim v (x - σ) -
        σ ^ 2 * deriv v x)
      (g' := fun σ => v (x + σ) - v (x - σ) - 2 * σ * deriv v x) (B := 2 * M * y ^ 2) hy
      (fun σ => by
        have := (((r19_hasDerivAt_add hPd x σ).sub_const (2 * ba_f1h_prim v x)).add
          (r19_hasDerivAt_sub hPd x σ)).sub ((hasDerivAt_pow 2 σ).mul_const (deriv v x))
        exact this.congr_deriv (by simp; ring))
      (fun σ hσ => (hφ σ hσ.1).trans (by have := pow_le_pow_left₀ hσ.1 hσ.2 2; nlinarith))
      (by simp; ring)
    calc _ ≤ 2 * M * y ^ 2 * y := h
      _ = 2 * M * y ^ 3 := by ring
  · have h := r19_mvt0 (g := fun σ => ba_f1h_prim v (x + σ) - ba_f1h_prim v (x - σ) - 2 * σ * v x)
      (g' := fun σ => v (x + σ) - 2 * v x + v (x - σ)) (B := 2 * M * y ^ 2) hy
      (fun σ => by
        have := ((r19_hasDerivAt_add hPd x σ).sub (r19_hasDerivAt_sub hPd x σ)).sub
          (((hasDerivAt_id σ).const_mul 2).mul_const (v x))
        exact this.congr_deriv (by simp; ring))
      (fun σ hσ => (hψ σ hσ.1).trans (by have := pow_le_pow_left₀ hσ.1 hσ.2 2; nlinarith))
      (by simp)
    calc _ ≤ 2 * M * y ^ 2 * y := h
      _ = 2 * M * y ^ 3 := by ring

/-- Monotonicity estimates: `A - B ≥ 2my` and `P(x+y) - 2P(x) + P(x-y) ≤ y (A - B)`. -/
theorem r19_mono_bounds {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) {m : ℝ} (hm : 0 < m) (hd : ∀ x, m ≤ deriv v x) (x : ℝ)
    {y : ℝ} (hy : 0 ≤ y) :
    2 * m * y ≤ v (x + y) - v (x - y) ∧
      ba_f1h_prim v (x + y) - 2 * ba_f1h_prim v x + ba_f1h_prim v (x - y) ≤ y * (v (x + y) - v (x - y)) := by
  obtain ⟨hd1, -, -⟩ := contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) v from hv)
  have hvd : ∀ s, HasDerivAt v (deriv v s) s := fun s => (hd1 s).hasDerivAt
  have hPd : ∀ s, HasDerivAt (ba_f1h_prim v) (v s) s := ba_f1h_prim_hasDerivAt hd1.continuous
  have hm0 : ∀ s, 0 ≤ s → 0 ≤ v (x + s) - v (x - s) - 2 * m * s := by
    intro s hs
    have hg : ∀ σ, HasDerivAt (fun σ => v (x + σ) - v (x - σ) - 2 * m * σ)
        (deriv v (x + σ) + deriv v (x - σ) - 2 * m) σ := by
      intro σ
      have := ((r19_hasDerivAt_add hvd x σ).sub (r19_hasDerivAt_sub hvd x σ)).sub
        ((hasDerivAt_id σ).const_mul (2 * m))
      exact this.congr_deriv (by simp)
    have hmono := monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun σ _ => (hg σ).continuousAt.continuousWithinAt) (fun σ _ => (hg σ).differentiableAt.differentiableWithinAt)
      (fun σ _ => by rw [(hg σ).deriv]; linarith [hd (x + σ), hd (x - σ)])
    have := hmono ((Set.mem_Ici.mpr (le_refl (0 : ℝ)))) (show s ∈ Ici (0 : ℝ) from hs) hs
    simpa using this
  refine ⟨by linarith [hm0 y hy], ?_⟩
  -- `θ(s) = P(x+s) - 2P(x) + P(x-s) - s (v(x+s) - v(x-s))` is antitone
  have hg : ∀ σ, HasDerivAt (fun σ => ba_f1h_prim v (x + σ) - 2 * ba_f1h_prim v x + ba_f1h_prim v (x - σ) -
      σ * (v (x + σ) - v (x - σ))) (-(σ * (deriv v (x + σ) + deriv v (x - σ)))) σ := by
    intro σ
    have := (((r19_hasDerivAt_add hPd x σ).sub_const (2 * ba_f1h_prim v x)).add (r19_hasDerivAt_sub hPd x σ)).sub
      ((hasDerivAt_id σ).mul ((r19_hasDerivAt_add hvd x σ).sub (r19_hasDerivAt_sub hvd x σ)))
    exact this.congr_deriv (by simp; ring)
  have hanti := antitoneOn_of_deriv_nonpos (convex_Ici 0)
    (fun σ _ => (hg σ).continuousAt.continuousWithinAt) (fun σ _ => (hg σ).differentiableAt.differentiableWithinAt)
    (fun σ hσ => by
      rw [(hg σ).deriv]
      have hσ0 : 0 ≤ σ := interior_subset hσ
      have h1 := hd (x + σ)
      have h2 := hd (x - σ)
      nlinarith [mul_nonneg hσ0 (show 0 ≤ deriv v (x + σ) + deriv v (x - σ) by linarith)])
  have := hanti ((Set.mem_Ici.mpr (le_refl (0 : ℝ)))) (show y ∈ Ici (0 : ℝ) from hy) hy
  simp only [add_zero, sub_zero, zero_mul, sub_self] at this
  linarith

/-- `dz`, `dz̄` from the real partials `f_x = a + ib`, `f_y = c + id`. -/
theorem r19_wirt {F : ℂ → ℂ} {z : ℂ} {a b c d : ℝ} (h1 : fderiv ℝ F z 1 = (a : ℂ) + (b : ℂ) * I)
    (hI : fderiv ℝ F z I = (c : ℂ) + (d : ℂ) * I) :
    dz F z = (((a + d) / 2 : ℝ) : ℂ) + (((b - c) / 2 : ℝ) : ℂ) * I ∧
      dzbar F z = (((a - d) / 2 : ℝ) : ℂ) + (((b + c) / 2 : ℝ) : ℂ) * I := by
  unfold dz dzbar
  rw [h1, hI]
  constructor <;> apply Complex.ext <;> simp <;> ring

theorem r19_norm_re_im (a b : ℝ) : ‖(a : ℂ) + (b : ℂ) * I‖ ≤ |a| + |b| := by
  calc ‖(a : ℂ) + (b : ℂ) * I‖ ≤ ‖(a : ℂ)‖ + ‖(b : ℂ) * I‖ := norm_add_le _ _
    _ = |a| + |b| := by simp [Complex.norm_real]

/-- (2) The `r = 2` Beurling–Ahlfors extension of a `C²` lift is asymptotically conformal at rate `O(Im z)`. -/
theorem r19_ba2_bound {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hp : ∀ x, v (x + 1) = v x + 1) {m : ℝ} (hm : 0 < m)
    (hd : ∀ x, m ≤ deriv v x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, 0 < z.im → ‖complexDilatation (beurlingAhlfors v 2) z‖ ≤ C * z.im := by
  obtain ⟨hd1, -, hv1⟩ := contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) v from hv)
  obtain ⟨hd2, -, hv2⟩ := contDiff_succ_iff_deriv.mp (show ContDiff ℝ (0 + 1) (deriv v) from hv1)
  have hc : Continuous v := hd1.continuous
  -- `v''` is `1`-periodic, hence bounded
  have hper1 : Function.Periodic (deriv v) 1 := GardinerLakic2000.gl16_deriv_periodic hp
  have hper2 : Function.Periodic (deriv (deriv v)) 1 := by
    intro x
    rw [← deriv_comp_add_const (deriv v) 1 x]
    have h2 : (fun y => deriv v (y + 1)) = deriv v := funext hper1
    rw [h2]
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hv2.continuous.continuousOn
  have hMb : ∀ s, |deriv (deriv v) s| ≤ M := by
    intro s
    obtain ⟨y, hy, he⟩ := hper2.exists_mem_Ico₀ one_pos s
    rw [he, ← Real.norm_eq_abs]
    exact hM y (Ico_subset_Icc_self hy)
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hMb 0)
  refine ⟨7 * M / m, by positivity, fun z hz => ?_⟩
  set x := z.re
  set y := z.im
  have hy0 : 0 < y := hz
  have hzU : z ∈ upperHalf := hz
  obtain ⟨hfx, hfy⟩ := ba_f1_partials hc hzU
  have hdiff : DifferentiableAt ℝ (beurlingAhlfors v 1) z :=
    ((ba_f1h_contDiffOn hc).contDiffAt (isOpen_upperHalf.mem_nhds hzU)).differentiableAt one_ne_zero
  have hF2 : beurlingAhlfors v 2 = s17p_stretch ∘ beurlingAhlfors v 1 := funext (s17p_ba2_apply v)
  have hfd : fderiv ℝ (beurlingAhlfors v 2) z = s17p_stretch.comp (fderiv ℝ (beurlingAhlfors v 1) z) := by
    rw [hF2]
    exact (s17p_stretch.hasFDerivAt.comp z hdiff.hasFDerivAt).fderiv
  have hst : ∀ p q : ℝ, s17p_stretch ((p : ℂ) + (q : ℂ) * I) = (p : ℂ) + ((2 * q : ℝ) : ℂ) * I := by
    intro p q
    apply Complex.ext
    · rw [(s17p_stretch_re_im _).1]; simp
    · rw [(s17p_stretch_re_im _).2]; simp
  set A := v (x + y)
  set B := v (x - y)
  set Cc := v x
  set P := ba_f1h_prim v
  have hI1 : (∫ t in (x - y)..(x + y), v t) = P (x + y) - P (x - y) := (ba_f1h_prim_sub hc _ _).symm
  have hI2 : (∫ t in x..(x + y), v t) - (∫ t in (x - y)..x, v t) = P (x + y) - 2 * P x + P (x - y) := by
    rw [← ba_f1h_prim_sub hc, ← ba_f1h_prim_sub hc]; ring
  set a : ℝ := (A - B) / (2 * y)
  set b : ℝ := 2 * ((A - 2 * Cc + B) / (2 * y))
  set c : ℝ := (A + B) / (2 * y) - (P (x + y) - P (x - y)) / (2 * y ^ 2)
  set d : ℝ := 2 * ((A - B) / (2 * y) - (P (x + y) - 2 * P x + P (x - y)) / (2 * y ^ 2))
  have h1 : fderiv ℝ (beurlingAhlfors v 2) z 1 = (a : ℂ) + (b : ℂ) * I := by
    rw [hfd, ContinuousLinearMap.comp_apply, hfx, hst]
  have hII : fderiv ℝ (beurlingAhlfors v 2) z I = (c : ℂ) + (d : ℂ) * I := by
    rw [hfd, ContinuousLinearMap.comp_apply, hfy, hI1, hI2, hst]
  obtain ⟨hdz, hdzbar⟩ := r19_wirt h1 hII
  obtain ⟨e1, e2, e3, e4⟩ := r19_second_diff hv hMb x hy0.le
  obtain ⟨l1, l2⟩ := r19_mono_bounds hv hm hd x hy0.le
  have hy2 : 0 < y ^ 2 := by positivity
  have ead : |a - d| ≤ 3 * M * y := by
    have e : a - d = -((A - B - 2 * y * deriv v x) / (2 * y)) +
        (P (x + y) - 2 * P x + P (x - y) - y ^ 2 * deriv v x) / y ^ 2 := by
      simp only [a, d]; field_simp; ring
    rw [e]
    calc _ ≤ |(A - B - 2 * y * deriv v x) / (2 * y)| +
          |(P (x + y) - 2 * P x + P (x - y) - y ^ 2 * deriv v x) / y ^ 2| := by
          rw [← abs_neg ((A - B - 2 * y * deriv v x) / (2 * y))]; exact abs_add_le _ _
      _ ≤ (2 * M * y ^ 2) / (2 * y) + (2 * M * y ^ 3) / y ^ 2 := by
          rw [abs_div, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * y), abs_of_pos hy2]
          exact add_le_add (div_le_div_of_nonneg_right e1 (by positivity))
            (div_le_div_of_nonneg_right e3 hy2.le)
      _ = 3 * M * y := by field_simp; ring
  have ebc : |b + c| ≤ 4 * M * y := by
    have e : b + c = (A - 2 * Cc + B) / y + (A - 2 * Cc + B) / (2 * y) -
        (P (x + y) - P (x - y) - 2 * y * Cc) / (2 * y ^ 2) := by
      simp only [b, c]; field_simp; ring
    rw [e]
    calc _ ≤ |(A - 2 * Cc + B) / y| + |(A - 2 * Cc + B) / (2 * y)| +
          |(P (x + y) - P (x - y) - 2 * y * Cc) / (2 * y ^ 2)| := by
          exact (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ (2 * M * y ^ 2) / y + (2 * M * y ^ 2) / (2 * y) + (2 * M * y ^ 3) / (2 * y ^ 2) := by
          rw [abs_div, abs_div, abs_div, abs_of_pos hy0, abs_of_pos (by positivity : (0 : ℝ) < 2 * y),
            abs_of_pos (by positivity : (0 : ℝ) < 2 * y ^ 2)]
          exact add_le_add (add_le_add (div_le_div_of_nonneg_right e2 hy0.le)
            (div_le_div_of_nonneg_right e2 (by positivity))) (div_le_div_of_nonneg_right e4 (by positivity))
      _ = 4 * M * y := by field_simp; ring
  have ead' : m ≤ a + d := by
    have e : a + d = 3 / 2 * ((A - B) / y) - (P (x + y) - 2 * P x + P (x - y)) / y ^ 2 := by
      simp only [a, d]; field_simp; ring
    rw [e]
    have hq : (P (x + y) - 2 * P x + P (x - y)) / y ^ 2 ≤ (A - B) / y := by
      rw [div_le_div_iff₀ hy2 hy0]; nlinarith
    have hab : 2 * m ≤ (A - B) / y := by rw [le_div_iff₀ hy0]; linarith
    linarith
  have hdzn : (a + d) / 2 ≤ ‖dz (beurlingAhlfors v 2) z‖ := by
    rw [hdz]
    have := Complex.re_le_norm ((((a + d) / 2 : ℝ) : ℂ) + (((b - c) / 2 : ℝ) : ℂ) * I)
    simpa using this
  have hdzbarn : ‖dzbar (beurlingAhlfors v 2) z‖ ≤ (|a - d| + |b + c|) / 2 := by
    rw [hdzbar]
    refine (r19_norm_re_im _ _).trans (le_of_eq ?_)
    rw [abs_div, abs_div, abs_two]; ring
  have hpos : 0 < (a + d) / 2 := by linarith
  unfold complexDilatation
  rw [norm_div]
  calc ‖dzbar (beurlingAhlfors v 2) z‖ / ‖dz (beurlingAhlfors v 2) z‖
      ≤ ((|a - d| + |b + c|) / 2) / ((a + d) / 2) :=
        div_le_div₀ (by positivity) hdzbarn hpos hdzn
    _ ≤ ((3 * M * y + 4 * M * y) / 2) / (m / 2) := by
        apply div_le_div₀ (by positivity) (by linarith) (by positivity) (by linarith)
    _ = 7 * M / m * y := by field_simp; ring

theorem r19_stretch_real (a : ℝ) : s17p_stretch (a : ℂ) = (a : ℂ) := by
  apply Complex.ext
  · rw [(s17p_stretch_re_im _).1]
  · rw [(s17p_stretch_re_im _).2]; simp

theorem r19_ba2_real (u : ℝ → ℝ) (x : ℝ) : beurlingAhlfors u 2 x = u x := by
  rw [s17p_ba2_apply, ba_f1h_real, r19_stretch_real]

theorem r19_ba2_im_lower {u : ℝ → ℝ} (hc : Continuous u) (hm : Monotone u) (hp : ∀ x, u (x + 1) = u x + 1)
    (z : ℂ) : z.im - 2 ≤ (beurlingAhlfors u 2 z).im := by
  rw [s17p_ba2_apply, (s17p_stretch_re_im _).2]
  have := beurlingAhlfors_im_linear_lower hc hm hp z
  linarith

theorem r19_disk_continuousAt_zero {u : ℝ → ℝ} (hc : Continuous u) (hm : Monotone u)
    (hp : ∀ x, u (x + 1) = u x + 1) :
    ContinuousAt (periodicDiskMap (beurlingAhlfors u 2)) 0 := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hC : 0 < Real.exp (4 * π) := Real.exp_pos _
  refine ⟨ε / Real.exp (4 * π), div_pos hε hC, ?_⟩
  intro z hz
  rw [periodicDiskMap_zero, dist_zero_right]
  by_cases hz0 : z = 0
  · simpa [hz0, periodicDiskMap_zero] using hε
  · have hh := r19_ba2_im_lower hc hm hp (diskCoverLog z)
    have hnorm : ‖diskCover (beurlingAhlfors u 2 (diskCoverLog z))‖ ≤
        Real.exp (4 * π) * ‖diskCover (diskCoverLog z)‖ := by
      rw [diskCover_norm, diskCover_norm, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hπ := Real.pi_pos
      nlinarith
    rw [← periodicDiskMap_cover (beurlingAhlfors_add_int hc hp 2), diskCover_log hz0] at hnorm
    rw [dist_zero_right] at hz
    have hbound := (lt_div_iff₀ hC).mp hz
    calc ‖periodicDiskMap (beurlingAhlfors u 2) z‖ ≤ Real.exp (4 * π) * ‖z‖ := hnorm
      _ < ε := by linarith

/-- (3) The descended `r = 2` extension is a quasiconformal self-map of `𝔻` with boundary values `h`. -/
theorem r19_disk_ext {h : ℂ → ℂ} {v : ℝ → ℝ} {ρ : ℝ} (hl : GardinerLakic2000.IsCircleLift h v)
    (hq : IsQuasisymmetric v ρ) :
    Continuous (periodicDiskMap (beurlingAhlfors v 2)) ∧ InjOn (periodicDiskMap (beurlingAhlfors v 2)) unitDisc ∧
      periodicDiskMap (beurlingAhlfors v 2) '' unitDisc = unitDisc ∧ periodicDiskMap (beurlingAhlfors v 2) 0 = 0 ∧
      EqOn (periodicDiskMap (beurlingAhlfors v 2)) h unitCircle ∧
      ∃ K, IsKQC (periodicDiskMap (beurlingAhlfors v 2)) unitDisc K := by
  obtain ⟨hc, hm, -, -, hp, he⟩ := hl
  have hBA := s17p_beurlingAhlfors_two hq
  let f := beurlingAhlfors v 2
  let G := periodicDiskMap f
  have hper : ∀ z : ℂ, ∀ n : ℤ, f (z + n) = f z + n := beurlingAhlfors_add_int hc hp 2
  have hGcont : Continuous G := by
    apply continuous_iff_continuousAt.mpr
    intro z
    by_cases hz : z = 0
    · subst z
      exact r19_disk_continuousAt_zero hc hm.monotone hp
    · exact periodicDiskMap_continuousAt_ne_zero (ba_f1h_continuous hc 2) hper hz
  have hG0 : G 0 = 0 := periodicDiskMap_zero _
  have hGp := periodicDiskMap_isKQC hBA.1 hper
  have hGpi := periodicDiskMap_injOn hper hBA.1.2.2.1.2.1
  have hGps := periodicDiskMap_image hper hBA.2.1
  have hGi : InjOn G unitDisc := by
    intro z hz w hw he
    by_cases hz0 : z = 0
    · subst z
      by_contra hw0
      exact periodicDiskMap_ne_zero (Ne.symm hw0) (he.symm.trans hG0)
    · by_cases hw0 : w = 0
      · subst w
        exact (periodicDiskMap_ne_zero hz0 (he.trans hG0)).elim
      · exact hGpi ⟨hz, hz0⟩ ⟨hw, hw0⟩ he
  have hGs : G '' unitDisc = unitDisc := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      by_cases hz0 : z = 0
      · simp [hz0, hG0, unitDisc]
      · have hh' : G z ∈ unitDisc \ {0} := hGps ▸ mem_image_of_mem _ ⟨hz, hz0⟩
        exact hh'.1
    · intro hw
      by_cases hw0 : w = 0
      · subst w
        exact ⟨0, by simp [unitDisc], hG0⟩
      · have hw' : w ∈ G '' (unitDisc \ {0}) := by rw [hGps]; exact ⟨hw, hw0⟩
        obtain ⟨z, hz, he⟩ := hw'
        exact ⟨z, hz.1, he⟩
  have hhome := qcl_f_isHomeomorphOnto_of_injOn isOpen_ball hGcont.continuousOn hGi
  have hGK : IsKQC G unitDisc (ρ ^ 2) := by
    apply iskqc_of_subsingleton_exceptional (P := fun z => z ∈ unitDisc ∧ z ≠ 0)
      isOpen_ball hhome hGp.2.1 (fun z hz => hz.1) ?_ hGp
    intro z hz w hw
    have hz0 : z = 0 := by by_contra hn; exact hz.2 ⟨hz.1, hn⟩
    have hw0 : w = 0 := by by_contra hn; exact hw.2 ⟨hw.1, hn⟩
    exact hz0.trans hw0.symm
  have hGb : EqOn G h unitCircle := by
    intro z hz
    obtain ⟨θ, hθ⟩ := Circle.exp_surjective (⟨z, mem_sphere_zero_iff_norm.mpr hz⟩ : Circle)
    have hθ' : exp ((θ : ℂ) * I) = z := by
      simpa only [Circle.coe_exp] using congrArg (fun ζ : Circle => (ζ : ℂ)) hθ
    let t : ℝ := θ / (2 * π)
    have ht : diskCover (t : ℂ) = z := by
      rw [diskCover]
      have hcθ : (2 * π * I : ℂ) * (t : ℂ) = (θ : ℂ) * I := by
        dsimp [t]
        push_cast
        field_simp
      rw [hcθ, hθ']
    rw [← ht]
    show periodicDiskMap f (diskCover (t : ℂ)) = h (diskCover (t : ℂ))
    rw [periodicDiskMap_cover hper, show f (t : ℂ) = (v t : ℂ) from r19_ba2_real v t]
    exact he t
  exact ⟨hGcont, hGi, hGs, hG0, hGb, _, hGK⟩

theorem r19_diskCover_deriv_ne_zero (a : ℂ) : deriv diskCover a ≠ 0 := by
  have : HasDerivAt diskCover (exp (2 * π * I * a) * (2 * π * I * 1)) a :=
    ((hasDerivAt_id a).const_mul (2 * π * I)).cexp
  rw [this.deriv]
  exact mul_ne_zero (exp_ne_zero _) (by rw [mul_one]; exact diskCoverCoeff_ne_zero)

/-- `|μ|` descends through `diskCover`: `|μ_{periodicDiskMap f}(e^{2πiz})| = |μ_f(z)|`. -/
theorem r19_disk_dil_pt {f : ℂ → ℂ} (hp : ∀ z : ℂ, ∀ n : ℤ, f (z + n) = f z + n) {z : ℂ}
    (hfd : DifferentiableAt ℝ f z) :
    ‖complexDilatation (periodicDiskMap f) (diskCover z)‖ = ‖complexDilatation f z‖ := by
  have hUi : InjOn diskCover (ball z (1 / 3)) := diskCover_injOn_ball z
  have hc : IsConformalOnto diskCover (ball z (1 / 3)) (diskCover '' ball z (1 / 3)) :=
    ⟨diskCover_differentiable.differentiableOn, hUi, rfl⟩
  have hVo := hc.isOpen isOpen_ball
  have hi := hc.symm isOpen_ball
  have hzU : z ∈ ball z (1 / 3) := mem_ball_self (by norm_num)
  have hwV : diskCover z ∈ diskCover '' ball z (1 / 3) := mem_image_of_mem _ hzU
  have hσz : Function.invFunOn diskCover (ball z (1 / 3)) (diskCover z) = z := hUi.leftInvOn_invFunOn hzU
  have heq : EqOn (periodicDiskMap f) (diskCover ∘ f ∘ Function.invFunOn diskCover (ball z (1 / 3)))
      (diskCover '' ball z (1 / 3)) := by
    rintro y ⟨x, hx, rfl⟩
    have hσx : Function.invFunOn diskCover (ball z (1 / 3)) (diskCover x) = x := hUi.leftInvOn_invFunOn hx
    simp only [Function.comp_apply]
    rw [hσx]
    exact periodicDiskMap_cover hp x
  have hσdiff : DifferentiableAt ℂ (Function.invFunOn diskCover (ball z (1 / 3))) (diskCover z) :=
    hi.1.differentiableAt (hVo.mem_nhds hwV)
  have hd1 : HasDerivAt diskCover (deriv diskCover z)
      (Function.invFunOn diskCover (ball z (1 / 3)) (diskCover z)) := by
    rw [hσz]; exact (diskCover_differentiable z).hasDerivAt
  have hcomp := hd1.comp (diskCover z) hσdiff.hasDerivAt
  have hid : HasDerivAt (diskCover ∘ Function.invFunOn diskCover (ball z (1 / 3))) 1 (diskCover z) := by
    apply (hasDerivAt_id (diskCover z)).congr_of_eventuallyEq
    filter_upwards [hVo.mem_nhds hwV] with y hy
    show diskCover (Function.invFunOn diskCover (ball z (1 / 3)) y) = y
    exact Function.invFunOn_eq hy
  have h1 := hcomp.unique hid
  have hσ' : deriv (Function.invFunOn diskCover (ball z (1 / 3))) (diskCover z) ≠ 0 :=
    right_ne_zero_of_mul_eq_one h1
  have hfσ : DifferentiableAt ℝ f (Function.invFunOn diskCover (ball z (1 / 3)) (diskCover z)) := by
    rw [hσz]; exact hfd
  have hfσc : DifferentiableAt ℝ (f ∘ Function.invFunOn diskCover (ball z (1 / 3))) (diskCover z) :=
    hfσ.comp _ (hσdiff.restrictScalars ℝ)
  rw [abR_t_complexDilatation_congr hVo heq hwV,
    complexDilatation_comp_conformal_left hfσc (diskCover_differentiable _) (r19_diskCover_deriv_ne_zero _),
    complexDilatation_comp_conformal_right hσdiff hσ' hfσ, hσz, norm_mul, norm_div, Complex.norm_conj,
    div_self (norm_ne_zero_iff.mpr hσ'), mul_one]

/-- (4) The bound of (2) transported to `𝔻` through `diskCover`. -/
theorem r19_disk_dilatation {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hp : ∀ x, v (x + 1) = v x + 1) {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ z : ℂ, 0 < z.im → ‖complexDilatation (beurlingAhlfors v 2) z‖ ≤ C * z.im) :
    ∀ᵐ w ∂(volume.restrict unitDisc),
      ‖complexDilatation (periodicDiskMap (beurlingAhlfors v 2)) w‖ ≤ C * (-Real.log ‖w‖ / (2 * π)) := by
  have _hC := hC
  have hc : Continuous v := hv.continuous
  have hper : ∀ z : ℂ, ∀ n : ℤ, beurlingAhlfors v 2 (z + n) = beurlingAhlfors v 2 z + n :=
    beurlingAhlfors_add_int hc hp 2
  have h0 : ∀ᵐ w ∂(volume.restrict unitDisc), w ∉ ({0} : Set ℂ) :=
    ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp (measure_singleton (0 : ℂ)))
  filter_upwards [h0, ae_restrict_mem (isOpen_ball.measurableSet : MeasurableSet unitDisc)] with w hw0 hwD
  have hw : w ∈ diskCover '' upperHalf := by rw [diskCover_image]; exact ⟨hwD, hw0⟩
  obtain ⟨z, hz, rfl⟩ := hw
  have hzU : z ∈ upperHalf := hz
  have hdiff : DifferentiableAt ℝ (beurlingAhlfors v 2) z := by
    have h1 : DifferentiableAt ℝ (beurlingAhlfors v 1) z :=
      ((ba_f1h_contDiffOn hc).contDiffAt (isOpen_upperHalf.mem_nhds hzU)).differentiableAt one_ne_zero
    have hF2 : beurlingAhlfors v 2 = s17p_stretch ∘ beurlingAhlfors v 1 := funext (s17p_ba2_apply v)
    rw [hF2]
    exact s17p_stretch.differentiableAt.comp z h1
  have hlog : -Real.log ‖diskCover z‖ / (2 * π) = z.im := by
    rw [diskCover_norm, Real.log_exp]
    field_simp
  rw [r19_disk_dil_pt hper hdiff, hlog]
  exact hb z hz

/-- Pointwise bound behind (5): `min(1, C log s)² ρ ≤ C²·1_{s ≤ 2} + K (1 + s)^{-4}` for `s = |z| > 1`. -/
theorem r19_L2_pointwise {C a s : ℝ} (hC : 0 ≤ C) (hs : 1 < s) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (ha : a ≤ C * Real.log s) :
    a ^ 2 * (4 / (1 - s ^ 2) ^ 2) ≤
      (if s ≤ 2 then C ^ 2 else 0) + (64 * 16 / 9) * (1 + s) ^ (-(4 : ℝ)) := by
  have hs1 : 0 < s - 1 := by linarith
  have hden : 0 < (1 - s ^ 2) ^ 2 := by
    have : 1 - s ^ 2 ≠ 0 := by nlinarith
    positivity
  have hq : (1 - s ^ 2) ^ 2 = (s - 1) ^ 2 * (s + 1) ^ 2 := by ring
  have hpow : (1 + s) ^ (-(4 : ℝ)) = ((1 + s) ^ 4)⁻¹ := by
    rw [Real.rpow_neg (by linarith), show ((4 : ℝ)) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hK : 0 ≤ (64 * 16 / 9) * (1 + s) ^ (-(4 : ℝ)) := by rw [hpow]; positivity
  by_cases h2 : s ≤ 2
  · rw [if_pos h2]
    have hlog : Real.log s ≤ s - 1 := by linarith [Real.log_le_sub_one_of_pos (by linarith : 0 < s)]
    have hlog0 : 0 ≤ Real.log s := Real.log_nonneg hs.le
    have haC : a ≤ C * (s - 1) := ha.trans (mul_le_mul_of_nonneg_left hlog hC)
    have hsq : a ^ 2 ≤ C ^ 2 * (s - 1) ^ 2 := by
      have := pow_le_pow_left₀ ha0 haC 2
      nlinarith
    have : a ^ 2 * (4 / (1 - s ^ 2) ^ 2) ≤ C ^ 2 := by
      rw [hq, mul_div_assoc', div_le_iff₀ (by positivity)]
      have h4 : 4 ≤ (s + 1) ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hsq (by norm_num : (0 : ℝ) ≤ 4), sq_nonneg C,
        mul_nonneg (sq_nonneg C) (sq_nonneg (s - 1))]
    linarith
  · rw [if_neg h2, zero_add]
    push_neg at h2
    have ha2 : a ^ 2 ≤ 1 := by nlinarith
    have hb : 4 / (1 - s ^ 2) ^ 2 ≤ (64 * 16 / 9) * ((1 + s) ^ 4)⁻¹ := by
      rw [← div_eq_mul_inv, div_le_div_iff₀ hden (by positivity)]
      have h1 : (1 + s) ^ 4 ≤ 16 * s ^ 4 := by
        have : 1 + s ≤ 2 * s := by linarith
        calc (1 + s) ^ 4 ≤ (2 * s) ^ 4 := pow_le_pow_left₀ (by linarith) this 4
          _ = 16 * s ^ 4 := by ring
      have h3 : 9 * s ^ 4 ≤ 16 * (1 - s ^ 2) ^ 2 := by
        have : 3 * s ^ 2 ≤ 4 * (s ^ 2 - 1) := by nlinarith
        nlinarith
      nlinarith
    rw [hpow]
    calc a ^ 2 * (4 / (1 - s ^ 2) ^ 2) ≤ 1 * (4 / (1 - s ^ 2) ^ 2) :=
          mul_le_mul_of_nonneg_right ha2 (by positivity)
      _ ≤ _ := by rw [one_mul]; exact hb

/-- (5) A Beltrami coefficient vanishing like `log|z|` at `S¹` is in `L²(𝔻*, ρ)`. -/
theorem r19_L2 {ν : LinfStar} (hν : ν ∈ LinfStarBall) {C : ℝ}
    (hb : ∀ᵐ z ∂(volume.restrict unitDiscExterior), ‖ν z‖ ≤ C * Real.log ‖z‖) :
    normL2 unitDiscExterior ν < ⊤ := by
  have hE : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  have hν1 : ‖ν‖ < 1 := mem_ball_zero_iff.mp hν
  set C' : ℝ := |C|
  have hC' : 0 ≤ C' := abs_nonneg C
  -- the dominating function
  let g : ℂ → ℝ := fun z => (if ‖z‖ ≤ 2 then C' ^ 2 else 0) + (64 * 16 / 9) * (1 + ‖z‖) ^ (-(4 : ℝ))
  have hgi : Integrable g volume := by
    have h1 : Integrable (fun z : ℂ => (64 * 16 / 9) * (1 + ‖z‖) ^ (-(4 : ℝ))) volume :=
      (integrable_one_add_norm (by rw [Complex.finrank_real_complex]; norm_num)).const_mul _
    have h2 : Integrable (fun z : ℂ => if ‖z‖ ≤ 2 then C' ^ 2 else 0) volume := by
      have : (fun z : ℂ => if ‖z‖ ≤ 2 then C' ^ 2 else 0) = (closedBall (0 : ℂ) 2).indicator (fun _ => C' ^ 2) := by
        funext z
        simp [Set.indicator, mem_closedBall_zero_iff]
      rw [this]
      exact (integrableOn_const (measure_closedBall_lt_top).ne).integrable_indicator measurableSet_closedBall
    exact h2.add h1
  have hlt : (∫⁻ z, ENNReal.ofReal (g z) ∂(volume.restrict unitDiscExterior)) < ⊤ :=
    hgi.restrict.lintegral_lt_top
  have hle : (∫⁻ z in unitDiscExterior, (‖ν z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)) ≤
      ∫⁻ z, ENNReal.ofReal (g z) ∂(volume.restrict unitDiscExterior) := by
    apply lintegral_mono_ae
    filter_upwards [hb, LinfStar_ae_norm_le ν, ae_restrict_mem hE] with z hz hz1 hzE
    have hs : 1 < ‖z‖ := hzE
    have ha : ‖ν z‖ ≤ C' * Real.log ‖z‖ :=
      hz.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.log_nonneg hs.le))
    have hp := r19_L2_pointwise hC' hs (norm_nonneg _) (hz1.trans hν1.le) ha
    rw [← enorm_eq_nnnorm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
      ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    unfold rho
    exact hp
  unfold normL2
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) (lt_of_le_of_lt hle hlt).ne

/-- (6) `eq19_exists_mu` (Ch1/Eq19Completed), with the Beltrami coefficient identified: copy of its body. -/
theorem r19_exists_mu {h : ℂ → ℂ} {K : ℝ} {e : ℂ ≃ₜ ℂ} (hH : IsKQC (⇑e) univ K)
    (hHc : e '' sphere (0 : ℂ) 1 = sphere (0 : ℂ) 1) (hHh : EqOn (⇑e) h unitCircle)
    (hm1 : h (-1) = -1) (hmI : h (-I) = -I) (h1 : h 1 = 1) :
    ∃ μ : LinfStar, μ ∈ LinfStarBall ∧
      (μ : ℂ → ℂ) =ᵐ[volume.restrict unitDiscExterior] complexDilatation (⇑e) ∧
      ∀ z : ℂ, ‖z‖ = 1 → wA μ z = h z := by
  have hK1 : (1 : ℝ) ≤ K := hH.2.1
  have hk0 : 0 ≤ (K - 1) / (K + 1) := div_nonneg (by linarith) (by linarith)
  have hk1 : (K - 1) / (K + 1) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  have hDo : IsOpen {w : ℂ | 1 < ‖w‖} := isOpen_lt continuous_const continuous_norm
  have hbd0 := (isKQC_maxDilatation_le hH).2
  have hbd : ∀ᵐ z ∂(volume.restrict unitDiscExterior),
      ‖complexDilatation (⇑e) z‖ ≤ (K - 1) / (K + 1) :=
    ae_restrict_of_ae_restrict_of_subset (subset_univ _) hbd0
  have hmeas : AEStronglyMeasurable (complexDilatation (⇑e)) (volume.restrict unitDiscExterior) :=
    (thm10_2_genHomeoSolution_of_isKQC hH).1.1.mono_measure
      (Measure.restrict_mono (subset_univ _) le_rfl)
  have hmem : MemLp (complexDilatation (⇑e)) ∞ (volume.restrict unitDiscExterior) :=
    memLp_top_of_bound hmeas _ hbd
  obtain ⟨μ, hμdef⟩ : ∃ μ : LinfStar, μ = toLinf (complexDilatation (⇑e)) := ⟨_, rfl⟩
  have hμae : (μ : ℂ → ℂ) =ᵐ[volume.restrict unitDiscExterior] complexDilatation (⇑e) := by
    rw [hμdef]
    exact bc_toLinf_ae hmem
  have hμ : μ ∈ LinfStarBall := by
    change μ ∈ ball (0 : LinfStar) 1
    rw [mem_ball_zero_iff, hμdef]
    exact lt_of_le_of_lt (norm_toLinf_le_of_ae_bound hk0 hbd) hk1
  refine ⟨μ, hμ, hμae, ?_⟩
  obtain ⟨Mμ, hMμ, Wμ, hWμ, hwfμ, hwiμ, hm1', hmI', hm2'⟩ := wA_spec hμ
  obtain ⟨KW, hKW⟩ := hWμ.1
  have hKWD := ac_t_isKQC_restrict hKW hDo (subset_univ _)
  have hKeD := ac_t_isKQC_restrict hH hDo (subset_univ _)
  have hdil : ∀ᵐ z ∂(volume.restrict {w : ℂ | 1 < ‖w‖}),
      complexDilatation Wμ z = complexDilatation (⇑e) z := by
    filter_upwards [ae_restrict_of_ae hWμ.2.2.2.2, hμae, ae_restrict_mem hDo.measurableSet]
      with z h1 h2 hz
    rw [h1, extA_eq_on_exterior μ hz]
    exact h2
  have hψ := bg_conformal_of_dilatation_eq hKeD hKWD hdil
  obtain ⟨hreg1, hreg2, hreg3⟩ := planeHomeomorph_circle_regions e hHc
  have hD : (⇑e) '' {w : ℂ | 1 < ‖w‖} = {w : ℂ | 1 < ‖w‖} := hreg3
  rw [hD] at hψ
  -- the sphere map
  have hE : ∀ u : ℂ, e.onePointCongr (u : ExtPlane) = ((e u : ℂ) : ExtPlane) := fun u => rfl
  have hEs : ∀ u : ℂ, e.onePointCongr.symm (u : ExtPlane) = ((e.symm u : ℂ) : ExtPlane) := by
    intro u
    exact e.onePointCongr.symm_apply_eq.2 (by rw [hE, e.apply_symm_apply])
  have hEinf : e.onePointCongr.symm extInf = extInf :=
    e.onePointCongr.symm_apply_eq.2 rfl
  have hEcl : ∀ q ∈ toExt (closedBall (0 : ℂ) 1), e.onePointCongr q ∈ toExt (closedBall (0 : ℂ) 1) := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨e v, hreg1 ▸ mem_image_of_mem e hv, rfl⟩
  have hEscl : ∀ p ∈ toExt (closedBall (0 : ℂ) 1),
      e.onePointCongr.symm p ∈ toExt (closedBall (0 : ℂ) 1) := by
    rintro _ ⟨u, hu, rfl⟩
    rw [hEs]
    rw [← hreg1] at hu
    obtain ⟨v, hv, rfl⟩ := hu
    refine ⟨v, hv, ?_⟩
    rw [e.symm_apply_apply]
  obtain ⟨Csph, hCdef⟩ : ∃ Csph : ExtPlane → ExtPlane,
      Csph = fun p => wAS μ (e.onePointCongr.symm p) := ⟨_, rfl⟩
  have hCcont : Continuous Csph := by
    rw [hCdef]
    exact (wAS_continuous hμ).comp e.onePointCongr.symm.continuous
  have hCinj : Function.Injective Csph := by
    intro p q hpq
    rw [hCdef] at hpq
    exact e.onePointCongr.symm.injective ((wAS_bijective μ).1 hpq)
  have hCnot : ∀ p ∉ toExt (closedBall (0 : ℂ) 1), Csph p ∉ toExt (closedBall (0 : ℂ) 1) := by
    intro p hp hC
    rw [hCdef] at hC
    have h2 := hEcl _ ((wAS_closed_iff hμ _).2 hC)
    rw [e.onePointCongr.apply_symm_apply] at h2
    exact hp h2
  have hCsurj : ∀ p' ∉ toExt (closedBall (0 : ℂ) 1), ∃ p ∉ toExt (closedBall (0 : ℂ) 1),
      Csph p = p' := by
    intro p' hp'
    obtain ⟨q, hq⟩ := (wAS_bijective μ).2 p'
    have hqn : q ∉ toExt (closedBall (0 : ℂ) 1) := by
      intro hqc
      apply hp'
      rw [← hq]
      exact (wAS_closed_iff hμ q).1 hqc
    refine ⟨e.onePointCongr q, ?_, ?_⟩
    · intro hc
      have h5 := hEscl _ hc
      rw [e.onePointCongr.symm_apply_apply] at h5
      exact hqn h5
    · rw [hCdef]
      show wAS μ (e.onePointCongr.symm (e.onePointCongr q)) = p'
      rw [e.onePointCongr.symm_apply_apply, hq]
  have hcirc : ∀ z : ℂ, ‖z‖ = 1 → e z = h z := fun z hz => hHh (show z ∈ unitCircle from hz)
  have hsymm : ∀ z : ℂ, ‖z‖ = 1 → e.symm (h z) = z := by
    intro z hz
    rw [← hcirc z hz, e.symm_apply_apply]
  have hfix1 : Csph ((-1 : ℂ) : ExtPlane) = ((-1 : ℂ) : ExtPlane) := by
    rw [hCdef]
    show wAS μ (e.onePointCongr.symm ((-1 : ℂ) : ExtPlane)) = _
    rw [hEs, ← hm1, hsymm (-1) (by simp), hm1]
    exact hm1'
  have hfixI : Csph ((-I : ℂ) : ExtPlane) = ((-I : ℂ) : ExtPlane) := by
    rw [hCdef]
    show wAS μ (e.onePointCongr.symm ((-I : ℂ) : ExtPlane)) = _
    rw [hEs, ← hmI, hsymm (-I) (by simp), hmI]
    exact hmI'
  have hfix2 : Csph ((1 : ℂ) : ExtPlane) = ((1 : ℂ) : ExtPlane) := by
    rw [hCdef]
    show wAS μ (e.onePointCongr.symm ((1 : ℂ) : ExtPlane)) = _
    rw [hEs, ← h1, hsymm 1 (by simp), h1]
    exact hm2'
  -- conformality of `c`
  have hσi : Function.Injective (mobiusExt 0 1 1 0) := fun a b h => by
    rw [← sigma_invol a, ← sigma_invol b, h]
  have hσ : IsMobius (mobiusExt 0 1 1 0) := ⟨0, 1, 1, 0, by norm_num, rfl⟩
  have hP : IsMobius (fun p => mobiusExt 0 1 1 0 (Mμ p)) := isMobius_comp hMμ hσ
  have hPc := mobius_finite_conformal hP
  obtain ⟨c, hcdef⟩ : ∃ c : ℂ → ℂ, c = fun w : ℂ =>
      finPart (mobiusExt 0 1 1 0 (Csph (mobiusExt 0 1 1 0 (w : ExtPlane)))) := ⟨_, rfl⟩
  have hinvon : ∀ u ∈ {w : ℂ | 1 < ‖w‖}, Function.invFunOn (⇑e) {w : ℂ | 1 < ‖w‖} u = e.symm u := by
    intro u hu
    rw [← hD] at hu
    obtain ⟨v, hv, rfl⟩ := hu
    rw [e.symm_apply_apply]
    exact (e.injective.injOn).leftInvOn_invFunOn hv
  obtain ⟨Ω, hΩ⟩ : ∃ Ω : Set ℂ, Ω = {w | w ∈ unitDisc ∧ w ≠ 0 ∧
      Csph (mobiusExt 0 1 1 0 (w : ExtPlane)) ≠ extInf} := ⟨_, rfl⟩
  have hcw : ∀ w ∈ Ω, w⁻¹ ∈ {w : ℂ | 1 < ‖w‖} ∧
      c w = finPart (mobiusExt 0 1 1 0 (Mμ (((Wμ ∘ Function.invFunOn (⇑e) {w : ℂ | 1 < ‖w‖}) w⁻¹ : ℂ) :
        ExtPlane))) ∧
      mobiusExt 0 1 1 0 (Mμ (((Wμ ∘ Function.invFunOn (⇑e) {w : ℂ | 1 < ‖w‖}) w⁻¹ : ℂ) : ExtPlane)) ≠
        extInf := by
    intro w hw
    rw [hΩ] at hw
    obtain ⟨hwD, hw0, hwne⟩ := hw
    have hwin : w⁻¹ ∈ {w : ℂ | 1 < ‖w‖} := by
      show 1 < ‖w⁻¹‖
      rw [norm_inv]
      have : ‖w‖ < 1 := mem_ball_zero_iff.1 hwD
      exact one_lt_inv₀ (norm_pos_iff.2 hw0) |>.2 this
    have hCw : Csph (mobiusExt 0 1 1 0 (w : ExtPlane)) =
        Mμ (((Wμ ∘ Function.invFunOn (⇑e) {w : ℂ | 1 < ‖w‖}) w⁻¹ : ℂ) : ExtPlane) := by
      rw [hCdef]
      show wAS μ (e.onePointCongr.symm (mobiusExt 0 1 1 0 (w : ExtPlane))) = _
      rw [sigma_coe hw0, hEs, Function.comp_apply, hinvon _ hwin]
      exact hwfμ _
    refine ⟨hwin, ?_, ?_⟩
    · rw [hcdef]
      show finPart (mobiusExt 0 1 1 0 (Csph (mobiusExt 0 1 1 0 (w : ExtPlane)))) = _
      rw [hCw]
    · rw [← hCw]
      obtain ⟨y, hy, -⟩ := sigma_of_not_closed (hCnot _ (sigma_not_closed hwD))
      rw [hy]
      exact OnePoint.coe_ne_infty y
  have hdiffΩ : DifferentiableOn ℂ c Ω := by
    have h1 : DifferentiableOn ℂ (fun w : ℂ => w⁻¹) Ω := fun w hw =>
      ((differentiableAt_id.inv (by
        rw [hΩ] at hw
        exact hw.2.1))).differentiableWithinAt
    have h2 : DifferentiableOn ℂ ((Wμ ∘ Function.invFunOn (⇑e) {w : ℂ | 1 < ‖w‖}) ∘ fun w : ℂ => w⁻¹) Ω :=
      hψ.1.comp h1 (fun w hw => (hcw w hw).1)
    have h3 := hPc.1.comp h2 (fun w hw => (hcw w hw).2.2)
    refine h3.congr (fun w hw => ?_)
    exact (hcw w hw).2.1
  have hE1 : {w : ℂ | w ∈ unitDisc ∧ Csph (mobiusExt 0 1 1 0 (w : ExtPlane)) = extInf}.Subsingleton := by
    intro w1 h1 w2 h2
    have := hCinj (h1.2.trans h2.2.symm)
    exact OnePoint.coe_injective (hσi this)
  have hEfin : (unitDisc \ Ω).Finite := by
    refine ((Set.finite_singleton (0 : ℂ)).union hE1.finite).subset ?_
    intro w hw
    by_cases h0 : w = 0
    · exact Or.inl h0
    · refine Or.inr ⟨hw.1, ?_⟩
      by_contra hb
      apply hw.2
      rw [hΩ]
      exact ⟨hw.1, h0, hb⟩
  have hdiffc : DifferentiableOn ℂ c unitDisc := by
    refine differentiableOn_of_finite_exceptional (show IsOpen unitDisc from isOpen_ball) hEfin ?_ ?_
    · rw [hcdef]
      exact sphere_c_continuousOn hCcont hCnot
    · refine hdiffΩ.mono ?_
      intro w hw
      by_contra h
      exact hw.2 ⟨hw.1, h⟩
  have hid := sphere_circle_id hCcont hCinj hCnot hCsurj (by rw [← hcdef]; exact hdiffc)
    hfix1 hfixI hfix2
  intro z hz
  have hez : ‖e z‖ = 1 := mem_sphere_zero_iff_norm.1 (hHc ▸ mem_image_of_mem e (mem_sphere_zero_iff_norm.2 hz))
  have h3 := hid (e z) hez
  rw [hCdef] at h3
  have h4 : wAS μ (z : ExtPlane) = ((e z : ℂ) : ExtPlane) := by
    have := h3
    simp only [hEs, e.symm_apply_apply] at this
    exact this
  show finPart (wAS μ (z : ExtPlane)) = h z
  rw [h4, ← hcirc z hz]
  rfl

/-- Clause 2 of Remark 1.9. -/
theorem r19_clause2 (p : T1) :
    (∃ u : ℝ → ℝ, ContDiff ℝ 3 u ∧ (∀ t, 0 < deriv u t) ∧ (∀ t, u (t + 2 * π) = u t + 2 * π) ∧
        ∀ t : ℝ, wA (Quotient.out p : LinfStarBall) (exp (t * I)) = exp (u t * I)) → p ∈ T01 := by
  rintro ⟨u, hu, hpos, hper, hh⟩
  have hμ0 := (Quotient.out p : LinfStarBall).property
  -- (1)–(3): the lift, the `O(Im z)` bound and the disc map
  obtain ⟨v, hl, hv2, ⟨m, hm, hd⟩, ρ, hq⟩ := r19_lift hu hpos hper hh
  have hl' := hl
  obtain ⟨-, -, -, -, hp, -⟩ := hl'
  obtain ⟨C, hC, hb⟩ := r19_ba2_bound hv2 hp hm hd
  obtain ⟨hGcont, hGi, hGs, hG0, hGb, K, hGK⟩ := r19_disk_ext hl hq
  have hdisk := r19_disk_dilatation hv2 hp hC hb
  -- the plane extension by reflection, keeping its dilatation
  have hQS : IsQSCircleHomeo (wA (Quotient.out p : LinfStarBall)) :=
    ⟨wA_circle_sensePreserving hμ0, wA_circle_quasisymmetric hμ0⟩
  have hunit : unitCircle = sphere (0 : ℂ) 1 := by ext z; simp [unitCircle]
  have hhi : InjOn (wA (Quotient.out p : LinfStarBall)) unitCircle := by
    rw [hunit]; exact hQS.2.choose_spec.1
  have hhs := sense_circle_image hQS.1
  have hExt := disk_map_closed_extension hGcont hGi hGs hGb hhi hhs
  obtain ⟨H, hHK, hHs, -, hHb, -, hHdil⟩ := ab_reflect hGK hGs hG0 hExt
  have hHh : EqOn H (wA (Quotient.out p : LinfStarBall)) unitCircle := by
    intro z hz
    have he := hHb z hz
    change (H z : ExtPlane) = (periodicDiskMap (beurlingAhlfors v 2) z : ExtPlane) at he
    exact (OnePoint.coe_injective he).trans (hGb hz)
  have hHc : H '' sphere (0 : ℂ) 1 = sphere (0 : ℂ) 1 := by
    rw [← hunit, image_congr hHh, hhs]
  obtain ⟨e, rfl⟩ := t1_homeomorph hHK hHs
  -- (6): a representative with `μ = μ_e` on `𝔻*`
  obtain ⟨M, -, W, -, -, -, hm1, hmI, hm2⟩ := wA_spec hμ0
  have hn1 : wA (Quotient.out p : LinfStarBall) (-1) = -1 := by
    show finPart (wAS _ ((-1 : ℂ) : ExtPlane)) = -1
    rw [hm1]; rfl
  have hnI : wA (Quotient.out p : LinfStarBall) (-I) = -I := by
    show finPart (wAS _ ((-I : ℂ) : ExtPlane)) = -I
    rw [hmI]; rfl
  have hn2 : wA (Quotient.out p : LinfStarBall) 1 = 1 := by
    show finPart (wAS _ ((1 : ℂ) : ExtPlane)) = 1
    rw [hm2]; rfl
  obtain ⟨μ, hμ, hμae, hwA⟩ := r19_exists_mu hHK hHc hHh hn1 hnI hn2
  have hPhi : Phi ⟨μ, hμ⟩ = p := by
    rw [← Quotient.out_eq p]
    exact Quotient.sound (fun z hz => hwA z hz)
  -- (4) through the reflection: `|μ(z)| ≤ C log|z| / (2π)` a.e. on `𝔻*`
  have hE : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  have hA := (ae_restrict_iff' (isOpen_ball.measurableSet : MeasurableSet unitDisc)).mp hdisk
  have hB := abT_ae_conj_inv hA
  have hbound : ∀ᵐ z ∂(volume.restrict unitDiscExterior), ‖μ z‖ ≤ C / (2 * π) * Real.log ‖z‖ := by
    filter_upwards [hμae, ae_restrict_of_ae hB, ae_restrict_of_ae hHdil, ae_restrict_mem hE] with z h1 h2 h3 hz
    have hz1 : 1 < ‖z‖ := hz
    have hn : ‖(conj z)⁻¹‖ = ‖z‖⁻¹ := by rw [norm_inv, Complex.norm_conj]
    have hin : (conj z)⁻¹ ∈ unitDisc :=
      mem_ball_zero_iff.mpr (by rw [hn]; exact inv_lt_one_of_one_lt₀ hz1)
    have h4 := h2 hin
    rw [hn, Real.log_inv, neg_neg] at h4
    rw [h1, h3 hz1]
    calc _ ≤ C * (Real.log ‖z‖ / (2 * π)) := h4
      _ = _ := by ring
  -- (5) and Cui's bound
  have hL2 := r19_L2 hμ hbound
  have hk1 : ‖μ‖ < 1 := mem_ball_zero_iff.mp hμ
  obtain ⟨C', -, hA2⟩ := CUI.cui_A2_bound (norm_nonneg μ) hk1
  have hfin : normA2 unitDisc (AInf.toFun (bersPhi μ)) < ⊤ :=
    lt_of_le_of_lt (hA2 μ le_rfl) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hL2)
  rw [TakhtajanTeo.cor_3_2]
  show AInf.toFun (bers p) ∈ A2fun unitDisc
  rw [← hPhi, bers_Phi]
  exact ⟨(bersPhi μ).2, hfin⟩

/-- **Remark 1.9** (TT:3660), byte-identical copy of `remark_1_9`. -/
theorem r19_remark_1_9 (p : T1) :
    ((∃ u : ℝ → ℝ, ContDiff ℝ 1 u ∧ (∀ t, 0 < deriv u t) ∧ (∀ t, u (t + 2 * π) = u t + 2 * π) ∧
        ∀ t : ℝ, wA (Quotient.out p : LinfStarBall) (exp (t * I)) = exp (u t * I)) → p ∈ symmetricT) ∧
      ((∃ u : ℝ → ℝ, ContDiff ℝ 3 u ∧ (∀ t, 0 < deriv u t) ∧ (∀ t, u (t + 2 * π) = u t + 2 * π) ∧
        ∀ t : ℝ, wA (Quotient.out p : LinfStarBall) (exp (t * I)) = exp (u t * I)) → p ∈ T01) :=
  ⟨w3_remark_1_9_clause1 p, r19_clause2 p⟩

/-- **Remark 1.9** (TT:3660).
- `S` contains the classes of `C¹`-diffeomorphisms of `S¹` [GS92].
- `T₀(1)` contains the classes of `C³`-diffeomorphisms (normalized as in (1.9)). -/
theorem remark_1_9 (p : T1) :
    ((∃ u : ℝ → ℝ, ContDiff ℝ 1 u ∧ (∀ t, 0 < deriv u t) ∧ (∀ t, u (t + 2 * π) = u t + 2 * π) ∧
        ∀ t : ℝ, wA (Quotient.out p : LinfStarBall) (exp (t * I)) = exp (u t * I)) → p ∈ symmetricT) ∧
      ((∃ u : ℝ → ℝ, ContDiff ℝ 3 u ∧ (∀ t, 0 < deriv u t) ∧ (∀ t, u (t + 2 * π) = u t + 2 * π) ∧
        ∀ t : ℝ, wA (Quotient.out p : LinfStarBall) (exp (t * I)) = exp (u t * I)) → p ∈ T01) :=
  r19_remark_1_9 p

end Ch2
end TakhtajanTeo
