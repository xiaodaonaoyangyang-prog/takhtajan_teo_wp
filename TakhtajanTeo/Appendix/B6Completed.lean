import TakhtajanTeo.Ch2.S2_Mixed
import TakhtajanTeo.Ch2.S2_Completed
import TakhtajanTeo.Ch2.S2_Completed4
import TakhtajanTeo.Ch2.S2_Completed5
import TakhtajanTeo.Appendix.B_PeriodMapping

/-!
# Appendix B completed originals, part 6 (`ab6_` copies)

`remark_B_6` (corrected statement) proved as `ab6_remark_B_6`, statement and docstring byte-identical to the original in
`B_PeriodMapping`. Conjuncts 1, 2, 3, 5 are the existing `brazD_schwarzian_bound`, `brazD_le_kerOpNorm`,
`kerOpNorm_kerK1_le_one`, `brazD_id_le_one`. Conjunct 4 (null complement ⇒ `‖K₁(f)‖ = 1`) is `ab6_conj4`: the area
theorem in its equality form for `U = Q₁(1/w)` (`ab6_area`: a copy of `mg_gap_green` with the outer curve a large
circle, `ab6_gap_green`; the `f`-side Laurent energy `ab6_f_side`; the `g`-side term `ab6_g_side`; the limits `ρ → 1`,
`K → ∞`), then the first column of the Grunsky matrix against `e₀` gives `‖K₁ e₀‖ ≥ 1`.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC Ch2
namespace AppB

theorem ab6_gap_green {f g : ℂ → ℂ} (hfd : DifferentiableOn ℂ f unitDisc) (hfi : InjOn f unitDisc)
    (hf0 : f 0 = 0) {K : ℝ} (hK : 0 < K) (hgdef : ∀ z, g z = (K : ℂ) * z) {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (hKb : ∀ z ∈ closedBall (0 : ℂ) ρ, ‖f z‖ < K)
    {U : ℂ → ℂ} (hU : DifferentiableOn ℂ U {0}ᶜ) :
    (((∫ w in (f '' closedBall (0 : ℂ) ρ ∪ g '' {z : ℂ | 1 / ρ ≤ ‖z‖})ᶜ, ‖deriv U w‖ ^ 2 : ℝ)) : ℂ) =
      -(1 / 2 : ℂ) * (∫ θ in (0 : ℝ)..2 * π,
        conj (U (f (circleMap 0 ρ θ))) * deriv (fun z => U (f z)) (circleMap 0 ρ θ) * circleMap 0 ρ θ) +
      (1 / 2 : ℂ) * (∫ θ in (0 : ℝ)..2 * π,
        conj (U (g (circleMap 0 (1 / ρ) θ))) * deriv (fun z => U (g z)) (circleMap 0 (1 / ρ) θ) *
          circleMap 0 (1 / ρ) θ) := by
  have hgfun : g = fun z : ℂ => (K : ℂ) * z := funext hgdef
  have hK0 : (K : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hK.ne'
  have hgu : IsUnivalentAtInfty g := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hgfun]; exact (differentiable_const _ |>.mul differentiable_id).differentiableOn
    · intro a _ b _ hab
      rw [hgdef, hgdef] at hab
      exact mul_left_cancel₀ hK0 hab
    · have : Tendsto (fun z : ℂ => (K : ℂ) * z) (cocompact ℂ) (cocompact ℂ) :=
        (Homeomorph.mulLeft₀ (K : ℂ) hK0).map_cocompact.le
      rw [hgfun]; exact this
  have hfarx : ∀ T : ℝ, 0 < T → ∃ R1 : ℝ, ∀ w : ℂ, R1 < ‖w‖ → ∃ z : ℂ, T ≤ ‖z‖ ∧ g z = w := by
    intro T hT
    refine ⟨K * T, fun w hw => ⟨w / K, ?_, ?_⟩⟩
    · rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hK.le, le_div_iff₀ hK]
      linarith
    · rw [hgdef]; field_simp
  have hfK : ∀ z ∈ closedBall (0 : ℂ) ρ, f z ∉ g '' unitDiscExterior := by
    rintro z hz ⟨u, hu, hzu⟩
    have h1 : 1 < ‖u‖ := hu
    have : K < ‖g u‖ := by
      rw [hgdef, norm_mul, Complex.norm_real, Real.norm_of_nonneg hK.le]
      nlinarith
    rw [hzu] at this
    exact absurd (hKb z hz) (not_lt.mpr this.le)
  have hdisjK : ∀ z ∈ closedBall (0 : ℂ) ρ, ∀ u ∈ unitDiscExterior, f z ≠ g u :=
    fun z hz u hu h0 => hfK z hz ⟨u, hu, h0.symm⟩
  have hR : 1 < 1 / ρ := one_lt_one_div hρ0 hρ1
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hUo : IsOpen unitDisc := isOpen_ball
  have h0D : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hg0 : ∀ w ∈ g '' unitDiscExterior, w ≠ 0 := by
    rintro w ⟨u, hu, rfl⟩ h0
    rw [hgdef] at h0
    have hu0 : u = 0 := (mul_eq_zero.mp h0).resolve_left hK0
    have h1 : 1 < ‖u‖ := hu
    rw [hu0, norm_zero] at h1
    exact absurd h1 (by norm_num)
  obtain ⟨cg, χ, hcg, hcg1, hcg0, hχ, hχg, hχ1⟩ := mg_gcut hgu hR
  -- the integrand
  have hU' : DifferentiableOn ℂ (deriv U) {0}ᶜ := hU.deriv isOpen_compl_singleton
  have hUs : ContDiffOn ℝ 1 U {0}ᶜ := (hU.contDiffOn isOpen_compl_singleton).restrict_scalars ℝ
  have hUs' : ContDiffOn ℝ 1 (deriv U) {0}ᶜ := (hU'.contDiffOn isOpen_compl_singleton).restrict_scalars ℝ
  set W : ℂ → ℂ := fun w => conj (U w) * deriv U w with hW
  have hWs : ContDiffOn ℝ 1 W {0}ᶜ :=
    ((Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp_contDiffOn hUs).mul hUs'
  set Φ : ℂ → ℂ := fun w => χ w * W w with hΦ
  have hΦs : ContDiffOn ℝ 1 Φ {0}ᶜ := hχ.contDiffOn.mul hWs
  have hgsub : g '' unitDiscExterior ⊆ {0}ᶜ := fun w hw => hg0 w hw
  have hgz : ∀ z : ℂ, 1 < ‖z‖ → g z ≠ 0 := fun z hz => hg0 _ ⟨z, hz, rfl⟩
  -- far support
  obtain ⟨R1, hR1⟩ := hfarx (2 * (1 / ρ)) (by positivity)
  have hfar : ∀ w : ℂ, |R1| + 1 ≤ ‖w‖ → Φ w = 0 := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := hR1 w (by linarith [le_abs_self R1])
    have hz1 : 1 < ‖z‖ := by linarith
    simp only [hΦ]
    rw [hχg z hz1, hcg0 z hz]
    simp
  obtain ⟨hFint, hFeq⟩ := mg_green_fchart hfd hfi hf0 hρ0 hρ1 hΦs hfar
  have hG := mg_green_gchart hgu hR (Φ := Φ) (hΦs.mono hgsub) (fun z hz => by
    have hz1 : 1 < ‖z‖ := by linarith
    simp only [hΦ]
    rw [hχg z hz1, hcg0 z hz]
    simp)
  -- regions
  set Kf : Set ℂ := f '' closedBall (0 : ℂ) ρ with hKf
  set Kg : Set ℂ := g '' {z : ℂ | 1 / ρ ≤ ‖z‖} with hKg
  have hKfc : IsCompact Kf := (isCompact_closedBall (0 : ℂ) ρ).image_of_continuousOn
    (hfd.continuousOn.mono (fun z hz => mem_ball_zero_iff.mpr
      (lt_of_le_of_lt (mem_closedBall_zero_iff.mp hz) hρ1)))
  have hKgc : IsClosed Kg := mg_image_closed hgu hR
  have hdKfKg : Disjoint Kf Kg := by
    rw [Set.disjoint_left]
    rintro w ⟨u, hu, rfl⟩ ⟨z, hz, hzu⟩
    have huD : u ∈ unitDisc := mem_ball_zero_iff.mpr (lt_of_le_of_lt (mem_closedBall_zero_iff.mp hu) hρ1)
    exact hdisjK u hu z (lt_of_lt_of_le hR hz) hzu.symm
  have hunion : (Kf ∪ Kg)ᶜ ∪ Kg = Kfᶜ := by
    ext w
    simp only [mem_union, mem_compl_iff]
    constructor
    · rintro (h1 | h1)
      · exact fun hf => h1 (Or.inl hf)
      · exact fun hf => Set.disjoint_left.mp hdKfKg hf h1
    · intro h1
      by_cases hw : w ∈ Kg
      · exact Or.inr hw
      · exact Or.inl (fun hh => hh.elim h1 hw)
  have hdisj2 : Disjoint (Kf ∪ Kg)ᶜ Kg := by
    rw [Set.disjoint_left]
    intro w hw hwg
    exact hw (Or.inr hwg)
  have hKgm : MeasurableSet Kg := hKgc.measurableSet
  have hGapm : MeasurableSet (Kf ∪ Kg)ᶜ := (hKfc.isClosed.union hKgc).measurableSet.compl
  have hint1 : IntegrableOn (dzbar Φ) (Kf ∪ Kg)ᶜ := by
    refine hFint.mono_set ?_
    rw [← hunion]; exact subset_union_left
  have hint2 : IntegrableOn (dzbar Φ) Kg := by
    refine hFint.mono_set ?_
    rw [← hunion]; exact subset_union_right
  have hsplit : ∫ w in Kfᶜ, dzbar Φ w = (∫ w in (Kf ∪ Kg)ᶜ, dzbar Φ w) + ∫ w in Kg, dzbar Φ w := by
    rw [← hunion]
    exact setIntegral_union hdisj2 hKgm hint1 hint2
  -- the gap integral
  have hgap : ∫ w in (Kf ∪ Kg)ᶜ, dzbar Φ w = (((∫ w in (Kf ∪ Kg)ᶜ, ‖deriv U w‖ ^ 2 : ℝ)) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun hGapm (fun w hw => ?_)
    have hw0 : w ≠ 0 := by
      intro h0
      exact hw (Or.inl ⟨0, by simp [hρ0.le], by rw [hf0, h0]⟩)
    have hev : Φ =ᶠ[𝓝 w] W := by
      filter_upwards [(hKfc.isClosed.union hKgc).isOpen_compl.mem_nhds hw] with u hu
      have hχu : χ u = 1 := by
        by_cases hug : u ∈ g '' unitDiscExterior
        · obtain ⟨z, hz, rfl⟩ := hug
          have hzR : ‖z‖ < 1 / ρ := by
            by_contra hge
            exact hu (Or.inr ⟨z, not_lt.mp hge, rfl⟩)
          rw [hχg z hz, hcg1 z hzR.le]
        · exact hχ1 u hug
      simp only [hΦ, hχu, one_mul]
    rw [dzbar_congr_of_eventuallyEq hev]
    exact g2_dzbar_conj_mul (hU.differentiableAt (isOpen_compl_singleton.mem_nhds hw0))
      (hU'.differentiableAt (isOpen_compl_singleton.mem_nhds hw0))
  -- boundary terms
  have hfb : (∮ z in C(0, ρ), Φ (f z) * deriv f z) = I * ∫ θ in (0 : ℝ)..2 * π,
      conj (U (f (circleMap 0 ρ θ))) * deriv (fun z => U (f z)) (circleMap 0 ρ θ) * circleMap 0 ρ θ := by
    rw [mg_circle_eq]
    congr 1
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    have hz : ‖circleMap 0 ρ θ‖ = ρ := by rw [norm_circleMap_zero, abs_of_pos hρ0]
    have hzD : circleMap 0 ρ θ ∈ unitDisc := mem_ball_zero_iff.mpr (by rw [hz]; exact hρ1)
    have hz0 : circleMap 0 ρ θ ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hz; exact hρ0.ne' hz.symm
    have hfz0 : f (circleMap 0 ρ θ) ≠ 0 := fun h0 =>
      hz0 (hfi hzD h0D (by rw [h0, hf0]))
    have hχf : χ (f (circleMap 0 ρ θ)) = 1 :=
      hχ1 _ (hfK _ (mem_closedBall_zero_iff.mpr (le_of_eq hz)))
    have hUd : DifferentiableAt ℂ U (f (circleMap 0 ρ θ)) :=
      hU.differentiableAt (isOpen_compl_singleton.mem_nhds hfz0)
    have hfdz : DifferentiableAt ℂ f (circleMap 0 ρ θ) := hfd.differentiableAt (hUo.mem_nhds hzD)
    have hch : deriv (fun z => U (f z)) (circleMap 0 ρ θ) =
        deriv U (f (circleMap 0 ρ θ)) * deriv f (circleMap 0 ρ θ) := deriv_comp _ hUd hfdz
    simp only [hΦ, hW]
    rw [hχf, hch]
    ring
  have hgb : (∮ z in C(0, 1 / ρ), Φ (g z) * deriv g z) = I * ∫ θ in (0 : ℝ)..2 * π,
      conj (U (g (circleMap 0 (1 / ρ) θ))) * deriv (fun z => U (g z)) (circleMap 0 (1 / ρ) θ) *
        circleMap 0 (1 / ρ) θ := by
    rw [mg_circle_eq]
    congr 1
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    have hz : ‖circleMap 0 (1 / ρ) θ‖ = 1 / ρ := by rw [norm_circleMap_zero, abs_of_pos (by positivity)]
    have hz1 : 1 < ‖circleMap 0 (1 / ρ) θ‖ := by rw [hz]; exact hR
    have hgz0 := hgz _ hz1
    have hUd : DifferentiableAt ℂ U (g (circleMap 0 (1 / ρ) θ)) :=
      hU.differentiableAt (isOpen_compl_singleton.mem_nhds hgz0)
    have hgdz : DifferentiableAt ℂ g (circleMap 0 (1 / ρ) θ) := hgu.1.differentiableAt (hEo.mem_nhds hz1)
    have hch : deriv (fun z => U (g z)) (circleMap 0 (1 / ρ) θ) =
        deriv U (g (circleMap 0 (1 / ρ) θ)) * deriv g (circleMap 0 (1 / ρ) θ) := deriv_comp _ hUd hgdz
    simp only [hΦ, hW]
    rw [hχg _ hz1, hcg1 _ (by rw [hz]), hch]
    ring
  rw [hfb] at hFeq
  rw [hgb] at hG
  set A : ℂ := ∫ θ in (0 : ℝ)..2 * π,
      conj (U (f (circleMap 0 ρ θ))) * deriv (fun z => U (f z)) (circleMap 0 ρ θ) * circleMap 0 ρ θ with hA
  set B : ℂ := ∫ θ in (0 : ℝ)..2 * π,
      conj (U (g (circleMap 0 (1 / ρ) θ))) * deriv (fun z => U (g z)) (circleMap 0 (1 / ρ) θ) *
        circleMap 0 (1 / ρ) θ with hB
  have hX : ∫ w in Kfᶜ, dzbar Φ w = -A / 2 := by
    have h1 : I * (2 * ∫ w in Kfᶜ, dzbar Φ w) = I * (-A) := by linear_combination hFeq
    have := mul_left_cancel₀ Complex.I_ne_zero h1
    linear_combination this / 2
  have hY : ∫ w in Kg, dzbar Φ w = -B / 2 := by
    have h1 : I * (2 * ∫ w in Kg, dzbar Φ w) = I * (-B) := by linear_combination hG
    have := mul_left_cancel₀ Complex.I_ne_zero h1
    linear_combination this / 2
  rw [← hgap]
  linear_combination (-1 : ℂ) * hsplit + hX - hY




/-- The `f`-side circle integral for a function `V` with Laurent expansion `V(f z) = z⁻¹ + c + Σ a(1, j+1) z^{j+1}`. -/
theorem ab6_f_side {f V : ℂ → ℂ} {a : ℕ → ℕ → ℂ} {c : ℂ}
    (hfd : DifferentiableOn ℂ f unitDisc)
    (hV : ∀ z ∈ unitDisc, z ≠ 0 →
      HasSum (fun m : ℕ => a 1 (m + 1) * z ^ (m + 1)) (V (f z) - c - z ^ (-(1 : ℤ))))
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) * (‖a 1 (j + 1)‖ ^ 2 * ρ ^ (2 * (j + 1)))) ∧
    (∫ θ in (0 : ℝ)..2 * π,
        conj (V (f (circleMap 0 ρ θ))) * deriv (fun z => V (f z)) (circleMap 0 ρ θ) *
          circleMap 0 ρ θ) =
      2 * π * ((((∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * (‖a 1 (j + 1)‖ ^ 2 * ρ ^ (2 * (j + 1)))) -
        (ρ ^ 2)⁻¹ : ℝ)) : ℂ) := by
  set F : ℕ → ℂ := fun n => if n = 0 then c else a 1 n with hF
  set G : ℕ → ℂ := fun n => if n = 1 then 1 else 0 with hG
  set d : ℤ → ℂ := fun n => if 0 ≤ n then F n.toNat else G (-n).toNat with hd
  obtain ⟨r1, hr1⟩ : ∃ r1 : ℝ, r1 = ρ / 2 := ⟨_, rfl⟩
  obtain ⟨r2, hr2⟩ : ∃ r2 : ℝ, r2 = (ρ + 1) / 2 := ⟨_, rfl⟩
  have hr1p : 0 < r1 := by rw [hr1]; positivity
  have hr1ρ : r1 < ρ := by rw [hr1]; linarith
  have hρr2 : ρ < r2 := by rw [hr2]; linarith
  have hr2one : r2 < 1 := by rw [hr2]; linarith
  have hdpos : ∀ n : ℕ, d (n : ℤ) = F n := fun n => by simp [hd]
  have hdneg : ∀ n : ℕ, d (-((n : ℤ) + 1)) = G (n + 1) := fun n => by
    have h1 : ¬ (0 : ℤ) ≤ -((n : ℤ) + 1) := by omega
    have h2 : (-(-((n : ℤ) + 1))).toNat = n + 1 := by omega
    simp only [hd, h1, if_false, h2]
  have hFs1 : ∀ n : ℕ, F (n + 1) = a 1 (n + 1) := fun n => by simp [hF]
  have hGn : ∀ n : ℕ, G (n + 1) = if n = 0 then 1 else 0 := fun n => by
    simp [hG]
  have hLaurent : ∀ w : ℂ, r1 < ‖w‖ → ‖w‖ < r2 → V (f w) = ∑' n : ℤ, d n * w ^ n := by
    intro w hw1 hw2
    have hwD : w ∈ unitDisc := mem_ball_zero_iff.mpr (hw2.trans hr2one)
    have hw0 : w ≠ 0 := by intro h0; rw [h0, norm_zero] at hw1; linarith
    have hS := hV w hwD hw0
    have hFsum : HasSum (fun n : ℕ => F n * w ^ n) ((V (f w) - c - w ^ (-(1 : ℤ))) + c) := by
      rw [← hasSum_nat_add_iff' 1]
      simp only [Finset.sum_range_one, hF, if_true, pow_zero, mul_one, add_sub_cancel_right]
      refine hS.congr_fun (fun n => ?_)
      simp
    have hGsum : HasSum (fun n : ℕ => G (n + 1) * w ^ (-((n : ℤ) + 1))) (w ^ (-(1 : ℤ))) := by
      have hh : HasSum (fun n : ℕ => G (n + 1) * w ^ (-((n : ℤ) + 1)))
          (G (0 + 1) * w ^ (-(((0 : ℕ) : ℤ) + 1))) :=
        hasSum_single 0 (fun n hn => by rw [hGn, if_neg hn, zero_mul])
      convert hh using 1
      rw [hGn, if_pos rfl]
      simp
    have htsum : ∑' n : ℤ, d n * w ^ n =
        ((V (f w) - c - w ^ (-(1 : ℤ))) + c) + w ^ (-(1 : ℤ)) :=
      (mg_hasSum_int F G hFsum hGsum).tsum_eq
    rw [htsum]
    ring
  have hpos : Summable (fun n : ℕ => ‖d n‖ * r2 ^ n) := by
    have hr2D : ((r2 : ℝ) : ℂ) ∈ unitDisc :=
      mem_ball_zero_iff.mpr (by rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]; exact hr2one)
    have hr20 : ((r2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
    have hS := hV _ hr2D hr20
    have hn := summable_norm_iff.mpr hS.summable
    rw [← summable_nat_add_iff 1]
    refine hn.congr (fun j => ?_)
    simp only [Nat.cast_add, Nat.cast_one]
    rw [show ((j : ℤ) + 1) = (((j + 1 : ℕ)) : ℤ) by push_cast; ring, hdpos, hFs1, norm_mul, norm_pow,
      Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hneg : Summable (fun n : ℕ => ‖d (-(n : ℤ))‖ * (r1 ^ n)⁻¹) := by
    refine summable_of_ne_finset_zero (s := Finset.range 2) (fun n hn => ?_)
    have hn' : 2 ≤ n := by simp at hn; omega
    have h1 : ¬ (0 : ℤ) ≤ -(n : ℤ) := by omega
    have h2 : (-(-(n : ℤ))).toNat = n := by omega
    have : d (-(n : ℤ)) = 0 := by
      simp only [hd, h1, if_false, h2, hG]
      rw [if_neg (by omega)]
    rw [this, norm_zero, zero_mul]
  have hE := mg_circle_energy (H := fun z => V (f z)) d hr1p hr1ρ hρr2 hpos hneg hLaurent
  obtain ⟨hgs, hTc⟩ := mg_energy_real hr1p hr1ρ hρr2 hpos hneg
  obtain ⟨hsp, hsn, hsplit⟩ := mg_energy_split hr1p hr1ρ hρr2 hpos hneg
  have e1 : (fun j : ℕ => ((j + 1 : ℕ) : ℝ) * (‖d ((j + 1 : ℕ) : ℤ)‖ ^ 2 * ρ ^ (2 * (j + 1)))) =
      fun j : ℕ => ((j + 1 : ℕ) : ℝ) * (‖a 1 (j + 1)‖ ^ 2 * ρ ^ (2 * (j + 1))) := by
    funext j
    rw [hdpos, hFs1]
  have e2 : ∀ k : ℕ, d (-((k + 1 : ℕ) : ℤ)) = if k = 0 then 1 else 0 := by
    intro k
    rw [show (-((k + 1 : ℕ) : ℤ)) = -((k : ℤ) + 1) by push_cast; ring, hdneg, hGn]
  rw [e1] at hsp
  refine ⟨hsp, ?_⟩
  rw [hE, hTc, hsplit, e1]
  have hneg2 : (∑' k : ℕ, ((k + 1 : ℕ) : ℝ) * (‖d (-((k + 1 : ℕ) : ℤ))‖ ^ 2 * (ρ ^ (2 * (k + 1)))⁻¹)) =
      (ρ ^ 2)⁻¹ := by
    rw [tsum_eq_single 0]
    · rw [e2]; simp
    · intro k hk
      rw [e2, if_neg hk]; simp
  rw [hneg2]



/-- The `g`-side boundary term for `V = q₁ w⁻¹` and `g = K·id`. -/
theorem ab6_g_side {q1 : ℂ} {K ρ : ℝ} (hK : 0 < K) (hρ0 : 0 < ρ) :
    (∫ θ in (0 : ℝ)..2 * π,
        conj ((fun w : ℂ => q1 * w⁻¹) ((K : ℂ) * circleMap 0 (1 / ρ) θ)) *
          deriv (fun z => (fun w : ℂ => q1 * w⁻¹) ((K : ℂ) * z)) (circleMap 0 (1 / ρ) θ) *
            circleMap 0 (1 / ρ) θ) = -(2 * π * ((‖q1‖ ^ 2 * ρ ^ 2 / K ^ 2 : ℝ) : ℂ)) := by
  have hK0 : (K : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hK.ne'
  have hpt : ∀ θ : ℝ, conj ((fun w : ℂ => q1 * w⁻¹) ((K : ℂ) * circleMap 0 (1 / ρ) θ)) *
      deriv (fun z => (fun w : ℂ => q1 * w⁻¹) ((K : ℂ) * z)) (circleMap 0 (1 / ρ) θ) *
        circleMap 0 (1 / ρ) θ = -((‖q1‖ ^ 2 * ρ ^ 2 / K ^ 2 : ℝ) : ℂ) := by
    intro θ
    have hz : ‖circleMap 0 (1 / ρ) θ‖ = 1 / ρ := by
      rw [norm_circleMap_zero, abs_of_pos (by positivity)]
    have hz0 : circleMap 0 (1 / ρ) θ ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hz
      exact (by positivity : (1 / ρ) ≠ 0) hz.symm
    set z := circleMap 0 (1 / ρ) θ with hzdef
    have hKz : (K : ℂ) * z ≠ 0 := mul_ne_zero hK0 hz0
    have hd : HasDerivAt (fun z : ℂ => q1 * ((K : ℂ) * z)⁻¹) (q1 * (-(((K : ℂ) * z) ^ 2)⁻¹ * K)) z := by
      have h1 : HasDerivAt (fun z : ℂ => (K : ℂ) * z) (K : ℂ) z := by
        simpa using (hasDerivAt_id z).const_mul (K : ℂ)
      have h2 := (hasDerivAt_inv hKz).comp z h1
      exact (h2.const_mul q1)
    rw [hd.deriv]
    have hzz : z * conj z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have hc0 : conj z ≠ 0 := (map_ne_zero _).mpr hz0
    have hq : q1 * conj q1 = ((‖q1‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [map_mul, map_inv₀, Complex.conj_ofReal]
    rw [hz] at hzz
    have hρ : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hρ0.ne'
    have hzz' : z * conj z = ((ρ : ℂ) ^ 2)⁻¹ := by
      rw [hzz]; push_cast; field_simp
    have hq' : conj q1 * q1 = ((‖q1‖ : ℂ)) ^ 2 := by
      rw [mul_comm, hq]; push_cast; ring
    push_cast
    field_simp
    rw [hq', mul_comm ((starRingEnd ℂ) z) z, hzz']
    field_simp
  rw [intervalIntegral.integral_congr (fun θ _ => hpt θ)]
  rw [intervalIntegral.integral_const, Complex.real_smul]
  rw [show (2 * π - 0 : ℝ) = 2 * π by ring]
  push_cast
  ring



/-- Area-theorem inequality for each radius `ρ < 1`. -/
theorem ab6_area_ineq {F : ℂ → ℂ} (hFd : DifferentiableOn ℂ F unitDisc) (hFi : InjOn F unitDisc)
    (hF0 : F 0 = 0) {a : ℕ → ℕ → ℂ} {q1 c : ℂ}
    (hV : ∀ z ∈ unitDisc, z ≠ 0 →
      HasSum (fun m : ℕ => a 1 (m + 1) * z ^ (m + 1))
        ((fun w : ℂ => q1 * w⁻¹) (F z) - c - z ^ (-(1 : ℤ))))
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    IntegrableOn (fun w : ℂ => (‖w‖ ^ 4)⁻¹) (F '' closedBall (0 : ℂ) ρ)ᶜ ∧
    π * ((ρ ^ 2)⁻¹ - ∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * (‖a 1 (j + 1)‖ ^ 2 * ρ ^ (2 * (j + 1)))) ≤
      ‖q1‖ ^ 2 * ∫ w in (F '' closedBall (0 : ℂ) ρ)ᶜ, (‖w‖ ^ 4)⁻¹ := by
  set V : ℂ → ℂ := fun w => q1 * w⁻¹ with hVdef
  set Kf : Set ℂ := F '' closedBall (0 : ℂ) ρ with hKf
  have hcbD : closedBall (0 : ℂ) ρ ⊆ unitDisc := by
    intro z hz
    exact mem_ball_zero_iff.mpr (lt_of_le_of_lt (mem_closedBall_zero_iff.mp hz) hρ1)
  have hbD : ball (0 : ℂ) ρ ⊆ unitDisc := ball_subset_closedBall.trans hcbD
  have hVd : DifferentiableOn ℂ V {0}ᶜ := fun w hw =>
    (differentiableAt_const q1 |>.mul (differentiableAt_inv (Set.mem_compl_singleton_iff.mp hw))).differentiableWithinAt
  have hderiv : ∀ w : ℂ, w ≠ 0 → ‖deriv V w‖ ^ 2 = ‖q1‖ ^ 2 * (‖w‖ ^ 4)⁻¹ := by
    intro w hw
    have hd : HasDerivAt V (q1 * (-(w ^ 2)⁻¹)) w := (hasDerivAt_inv hw).const_mul q1
    rw [hd.deriv, norm_mul, norm_neg, norm_inv, norm_pow]
    have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
    field_simp
  -- a ball around `0` inside `Kf`
  have hopen : IsOpen (F '' ball (0 : ℂ) ρ) :=
    (RMT.differentiableOn_invFunOn_of_injOn isOpen_ball (hFd.mono hbD) (hFi.mono hbD)).1
  have h0mem : (0 : ℂ) ∈ F '' ball (0 : ℂ) ρ := ⟨0, mem_ball_self hρ0, hF0⟩
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp hopen 0 h0mem
  have hballKf : ball (0 : ℂ) ε ⊆ Kf :=
    hεsub.trans (Set.image_mono ball_subset_closedBall)
  have hsubε : Kfᶜ ⊆ {ω : ℂ | ε ≤ ‖ω - 0‖} := by
    intro w hw
    by_contra hlt
    exact hw (hballKf (mem_ball_zero_iff.mpr (by simpa [not_le] using hlt)))
  have hint0 := (s2c_l4_outside_ball 0 hε).1
  have hint : IntegrableOn (fun w : ℂ => (‖w‖ ^ 4)⁻¹) Kfᶜ := by
    have := hint0.mono_set hsubε
    simpa only [sub_zero] using this
  have hKfc : IsCompact Kf := (isCompact_closedBall (0 : ℂ) ρ).image_of_continuousOn
    (hFd.continuousOn.mono hcbD)
  have hKfm : MeasurableSet Kfᶜ := hKfc.isClosed.measurableSet.compl
  have h0Kf : (0 : ℂ) ∈ Kf := ⟨0, by simp [hρ0.le], hF0⟩
  refine ⟨hint, ?_⟩
  -- bound of `F` on the closed ball
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) ρ).exists_bound_of_continuousOn
    (hFd.continuousOn.mono hcbD)
  set E : ℝ := ∫ w in Kfᶜ, (‖w‖ ^ 4)⁻¹ with hE
  have hV' : IntegrableOn (fun w => ‖deriv V w‖ ^ 2) Kfᶜ := by
    refine (show IntegrableOn (fun w : ℂ => ‖q1‖ ^ 2 * (‖w‖ ^ 4)⁻¹) Kfᶜ volume from hint.const_mul (‖q1‖ ^ 2)).congr_fun
      (fun w hw => ?_) hKfm
    exact (hderiv w (fun h0 => hw (h0 ▸ h0Kf))).symm
  have hEint : ∫ w in Kfᶜ, ‖deriv V w‖ ^ 2 = ‖q1‖ ^ 2 * E := by
    rw [hE, ← integral_const_mul]
    exact setIntegral_congr_fun hKfm (fun w hw => hderiv w (fun h0 => hw (h0 ▸ h0Kf)))
  have hK : ∀ K : ℝ, max C 0 + 1 ≤ K →
      π * ((ρ ^ 2)⁻¹ - ∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * (‖a 1 (j + 1)‖ ^ 2 * ρ ^ (2 * (j + 1)))) ≤
        ‖q1‖ ^ 2 * E + π * (‖q1‖ ^ 2 * ρ ^ 2 / K ^ 2) := by
    intro K hKK
    have hKpos : 0 < K := lt_of_lt_of_le (by positivity) hKK
    have hKb : ∀ z ∈ closedBall (0 : ℂ) ρ, ‖F z‖ < K := fun z hz =>
      lt_of_le_of_lt ((hC z hz).trans (le_max_left C 0)) (by linarith)
    have hgreen := ab6_gap_green (g := fun z : ℂ => (K : ℂ) * z) hFd hFi hF0 hKpos (fun z => rfl)
      hρ0 hρ1 hKb (U := V) hVd
    obtain ⟨hSs, hfs⟩ := ab6_f_side hFd hV hρ0 hρ1
    have hgs := ab6_g_side (q1 := q1) hKpos hρ0
    set S : ℝ := ∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * (‖a 1 (j + 1)‖ ^ 2 * ρ ^ (2 * (j + 1))) with hS
    have hgreen' : (((∫ w in (Kf ∪ (fun z : ℂ => (K : ℂ) * z) '' {z : ℂ | 1 / ρ ≤ ‖z‖})ᶜ,
        ‖deriv V w‖ ^ 2 : ℝ)) : ℂ) =
        -(1 / 2 : ℂ) * (2 * π * (((S - (ρ ^ 2)⁻¹ : ℝ)) : ℂ)) +
          (1 / 2 : ℂ) * (-(2 * π * ((‖q1‖ ^ 2 * ρ ^ 2 / K ^ 2 : ℝ) : ℂ))) := by
      rw [← hfs, ← hgs]
      exact hgreen
    have hreal : (∫ w in (Kf ∪ (fun z : ℂ => (K : ℂ) * z) '' {z : ℂ | 1 / ρ ≤ ‖z‖})ᶜ,
        ‖deriv V w‖ ^ 2 : ℝ) = π * ((ρ ^ 2)⁻¹ - S) - π * (‖q1‖ ^ 2 * ρ ^ 2 / K ^ 2) := by
      apply Complex.ofReal_injective
      rw [hgreen']
      push_cast
      ring
    have hKgc : IsClosed ((fun z : ℂ => (K : ℂ) * z) '' {z : ℂ | 1 / ρ ≤ ‖z‖}) := by
      have hgu : IsUnivalentAtInfty (fun z : ℂ => (K : ℂ) * z) := by
        have hK0 : (K : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hKpos.ne'
        refine ⟨(differentiable_const _ |>.mul differentiable_id).differentiableOn, ?_,
          (Homeomorph.mulLeft₀ (K : ℂ) hK0).map_cocompact.le⟩
        intro x _ y _ hxy
        exact mul_left_cancel₀ hK0 hxy
      exact mg_image_closed hgu (one_lt_one_div hρ0 hρ1)
    have hmono : (∫ w in (Kf ∪ (fun z : ℂ => (K : ℂ) * z) '' {z : ℂ | 1 / ρ ≤ ‖z‖})ᶜ,
        ‖deriv V w‖ ^ 2) ≤ ∫ w in Kfᶜ, ‖deriv V w‖ ^ 2 :=
      setIntegral_mono_set hV' (Filter.Eventually.of_forall (fun w => sq_nonneg _))
        (HasSubset.Subset.eventuallyLE (Set.compl_subset_compl.mpr Set.subset_union_left))
    rw [hEint, hreal] at hmono
    linarith
  have hlim : Tendsto (fun K : ℝ => ‖q1‖ ^ 2 * E + π * (‖q1‖ ^ 2 * ρ ^ 2 / K ^ 2)) atTop
      (𝓝 (‖q1‖ ^ 2 * E)) := by
    have h1 : Tendsto (fun K : ℝ => (‖q1‖ ^ 2 * ρ ^ 2) / K ^ 2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop two_ne_zero)
    simpa using (tendsto_const_nhds (x := ‖q1‖ ^ 2 * E)).add (h1.const_mul π)
  exact ge_of_tendsto hlim (Filter.eventually_atTop.mpr ⟨max C 0 + 1, hK⟩)



/-- Area theorem, equality direction: if `ℂ \ F(𝔻)` is null then `Σ (j+1) |a(1, j+1)|² ≥ 1`. -/
theorem ab6_area {F : ℂ → ℂ} (hFd : DifferentiableOn ℂ F unitDisc) (hFi : InjOn F unitDisc)
    (hF0 : F 0 = 0) (hF1 : deriv F 0 = 1) (hnull : volume (F '' unitDisc)ᶜ = 0)
    {a : ℕ → ℕ → ℂ} (hsym : ∀ m n, a m n = a n m)
    (hexp : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w → ∃ S : ℂ,
      HasSum (fun p : ℕ × ℕ => a p.1 p.2 * z ^ p.1 * w ^ p.2) S ∧
        (F z - F w) / (z - w) = exp (0 - S))
    (hsumm : Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) * ‖a 1 (j + 1)‖ ^ 2)) :
    1 ≤ ∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * ‖a 1 (j + 1)‖ ^ 2 := by
  obtain ⟨Q, hQd, hQ⟩ := faber_negative_polynomials hFd hFi hF0 hF1 (b00 := 0) hsym hexp
  obtain ⟨q1, q0, hq⟩ : ∃ q1 q0 : ℂ,
      Q (0 + 1) = Polynomial.C q1 * Polynomial.X + Polynomial.C q0 :=
    Polynomial.exists_eq_X_add_C_of_natDegree_le_one ((hQd 0).le.trans (by norm_num))
  have hV : ∀ z ∈ unitDisc, z ≠ 0 →
      HasSum (fun m : ℕ => a 1 (m + 1) * z ^ (m + 1))
        ((fun w : ℂ => q1 * w⁻¹) (F z) - (-q0) - z ^ (-(1 : ℤ))) := by
    intro z hz hz0
    have h := hQ 0 z hz hz0
    rw [hq] at h
    simp only [Nat.cast_add, Nat.cast_zero, zero_add, Nat.cast_one, one_mul, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Int.cast_one, neg_inj] at h
    convert h using 1
    ring
  let ρn : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 2)
  have hρ0 : ∀ n, 0 < ρn n := fun n => by
    simp only [ρn]
    have : 1 / ((n : ℝ) + 2) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    linarith
  have hρ1 : ∀ n, ρn n < 1 := fun n => by
    simp only [ρn]
    have : 0 < 1 / ((n : ℝ) + 2) := by positivity
    linarith
  have hρmono : Monotone ρn := by
    intro m n hmn
    simp only [ρn]
    have : 1 / ((n : ℝ) + 2) ≤ 1 / ((m : ℝ) + 2) :=
      one_div_le_one_div_of_le (by positivity) (by simpa using (Nat.cast_le (α := ℝ)).mpr hmn)
    linarith
  have hρlim : Tendsto ρn atTop (𝓝 1) := by
    have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      refine h1.inv_tendsto_atTop.congr (fun n => ?_)
      simp [one_div]
    simpa [ρn] using (tendsto_const_nhds (x := (1 : ℝ))).sub h2
  have hineq := fun n => ab6_area_ineq hFd hFi hF0 hV (hρ0 n) (hρ1 n)
  -- the exterior energies tend to `0`
  have hEn : Tendsto (fun n => ∫ w in (F '' closedBall (0 : ℂ) (ρn n))ᶜ, (‖w‖ ^ 4)⁻¹) atTop (𝓝 0) := by
    have hsm : ∀ n, MeasurableSet (F '' closedBall (0 : ℂ) (ρn n))ᶜ := fun n => by
      have hcbD : closedBall (0 : ℂ) (ρn n) ⊆ unitDisc := fun z hz =>
        mem_ball_zero_iff.mpr (lt_of_le_of_lt (mem_closedBall_zero_iff.mp hz) (hρ1 n))
      exact ((isCompact_closedBall (0 : ℂ) (ρn n)).image_of_continuousOn
        (hFd.continuousOn.mono hcbD)).isClosed.measurableSet.compl
    have hanti : Antitone (fun n => (F '' closedBall (0 : ℂ) (ρn n))ᶜ) := by
      intro m n hmn
      exact Set.compl_subset_compl.mpr (Set.image_mono (closedBall_subset_closedBall (hρmono hmn)))
    have h := tendsto_setIntegral_of_antitone (μ := volume) (f := fun w : ℂ => (‖w‖ ^ 4)⁻¹) hsm hanti
      ⟨0, (hineq 0).1⟩
    have hI : (⋂ n, (F '' closedBall (0 : ℂ) (ρn n))ᶜ) = (F '' unitDisc)ᶜ := by
      ext w
      simp only [mem_iInter, mem_compl_iff, mem_image]
      constructor
      · rintro hw ⟨z, hz, rfl⟩
        obtain ⟨n, hn⟩ : ∃ n : ℕ, ‖z‖ ≤ ρn n := by
          have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
          have := hρlim.eventually (lt_mem_nhds hz1)
          obtain ⟨n, hn⟩ := this.exists
          exact ⟨n, hn.le⟩
        exact hw n ⟨z, mem_closedBall_zero_iff.mpr hn, rfl⟩
      · rintro hw n ⟨z, hz, rfl⟩
        exact hw ⟨z, mem_ball_zero_iff.mpr (lt_of_le_of_lt (mem_closedBall_zero_iff.mp hz) (hρ1 n)), rfl⟩
    rw [hI, setIntegral_measure_zero _ hnull] at h
    exact h
  -- the series tend to the full sum
  have hSn : Tendsto (fun n => ∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * (‖a 1 (j + 1)‖ ^ 2 * ρn n ^ (2 * (j + 1))))
      atTop (𝓝 (∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * ‖a 1 (j + 1)‖ ^ 2)) := by
    have := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
      (f := fun n (j : ℕ) => ((j + 1 : ℕ) : ℝ) * (‖a 1 (j + 1)‖ ^ 2 * ρn n ^ (2 * (j + 1))))
      (g := fun j => ((j + 1 : ℕ) : ℝ) * ‖a 1 (j + 1)‖ ^ 2) (bound := fun j => ((j + 1 : ℕ) : ℝ) * ‖a 1 (j + 1)‖ ^ 2)
      hsumm
      (fun j => by
        have h1 : Tendsto (fun n => ρn n ^ (2 * (j + 1))) atTop (𝓝 (1 ^ (2 * (j + 1)))) :=
          hρlim.pow _
        simpa using (h1.const_mul (‖a 1 (j + 1)‖ ^ 2)).const_mul (((j + 1 : ℕ) : ℝ)))
      (Filter.Eventually.of_forall (fun n j => by
        have h0 : 0 ≤ ρn n ^ (2 * (j + 1)) := pow_nonneg (hρ0 n).le _
        have h1 : ρn n ^ (2 * (j + 1)) ≤ 1 := pow_le_one₀ (hρ0 n).le (hρ1 n).le
        rw [Real.norm_of_nonneg (by positivity)]
        have : 0 ≤ ((j + 1 : ℕ) : ℝ) * ‖a 1 (j + 1)‖ ^ 2 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ ((j + 1 : ℕ) : ℝ) * ‖a 1 (j + 1)‖ ^ 2)]))
    exact this
  have hinv : Tendsto (fun n => (ρn n ^ 2)⁻¹) atTop (𝓝 1) := by
    simpa using ((hρlim.pow 2).inv₀ (by norm_num))
  have hL : Tendsto (fun n => π * ((ρn n ^ 2)⁻¹ - ∑' j : ℕ, ((j + 1 : ℕ) : ℝ) *
      (‖a 1 (j + 1)‖ ^ 2 * ρn n ^ (2 * (j + 1))))) atTop
      (𝓝 (π * (1 - ∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * ‖a 1 (j + 1)‖ ^ 2))) :=
    (hinv.sub hSn).const_mul π
  have hR : Tendsto (fun n => ‖q1‖ ^ 2 * ∫ w in (F '' closedBall (0 : ℂ) (ρn n))ᶜ, (‖w‖ ^ 4)⁻¹)
      atTop (𝓝 (‖q1‖ ^ 2 * 0)) := hEn.const_mul _
  have hle := le_of_tendsto_of_tendsto' hL hR (fun n => (hineq n).2)
  rw [mul_zero] at hle
  have := Real.pi_pos
  nlinarith



/-- The normalized case of conjunct 4: the first Grunsky column has norm one. -/
theorem ab6_opNorm_ge {F : ℂ → ℂ} (hFd : DifferentiableOn ℂ F unitDisc) (hFi : InjOn F unitDisc)
    (hF0 : F 0 = 0) (hF1 : deriv F 0 = 1) (hnull : volume (F '' unitDisc)ᶜ = 0) :
    1 ≤ kerOpNorm (kerK1 F) := by
  obtain ⟨a, hsym, hexp, hker⟩ := g2c_normalized_kernel_series_exists hFd hFi hF1
  have hB := g2c_grunsky_matrix_contraction hFd hFi hsym hexp
  set B : ℕ → ℕ → ℂ := fun m n => (Real.sqrt (((m : ℝ) + 1) * ((n : ℝ) + 1)) : ℂ) * a (m + 1) (n + 1)
    with hBdef
  have hsB : ∀ m n, B m n = B n m := by
    intro m n
    simp only [hBdef, hsym (m + 1) (n + 1), mul_comm ((m : ℝ) + 1)]
  have hK : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w →
      HasSum (fun p : ℕ × ℕ => B p.1 p.2 * basisE p.1 z * basisE p.2 w) (kerK1 F z w) := by
    intro x hx w hw hxw
    have hh := (hker x hx w hw hxw).div_const (π : ℂ)
    have hp : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    rw [show ((π : ℂ) * kerK1 F x w) / (π : ℂ) = kerK1 F x w by field_simp] at hh
    exact hh.congr_fun (fun p => g2c_basis_weight a p.1 p.2 x w)
  have hcontr : B7Contractive B := fun x hx => ⟨(hB.2 x hx).2.1, (hB.2 x hx).2.2⟩
  have hB0 : ∀ n : ℕ, ‖B 0 n‖ ^ 2 = ((n + 1 : ℕ) : ℝ) * ‖a 1 (n + 1)‖ ^ 2 := by
    intro n
    simp only [hBdef, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow]
    rw [Real.sq_sqrt (by positivity)]
    push_cast
    simp
  have hsumm : Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) * ‖a 1 (j + 1)‖ ^ 2) :=
    ((hB.1 0).1).congr hB0
  have hS := ab6_area hFd hFi hF0 hF1 hnull hsym hexp hsumm
  -- the test function `ψ = e₀`
  set x : ℕ → ℂ := fun n => if n = 0 then (1 : ℂ) else 0 with hxdef
  have hx : Summable (fun n => ‖x n‖ ^ 2) :=
    summable_of_ne_finset_zero (s := {0}) (fun n hn => by simp [hxdef, Finset.mem_singleton.not.mp hn |> fun h => h])
  have hxs : ∑' n, ‖x n‖ ^ 2 = 1 := by
    rw [tsum_eq_single 0]
    · simp [hxdef]
    · intro n hn; simp [hxdef, hn]
  obtain ⟨hψ, hψn⟩ := bergman_ell2_series hx
  set ψ : ℂ → ℂ := fun z => ∑' n, x n * basisE n z with hψdef
  have hxe : ∀ z ∈ unitDisc, HasSum (fun n => x n * basisE n z) (ψ z) := fun z hz =>
    (bergman_pair_summable hx (basisE_sq_summable hz)).of_norm.hasSum
  have hxc : Summable (fun n => ‖conj (x n)‖ ^ 2) := by simpa only [Complex.norm_conj] using hx
  obtain ⟨hT, hTe⟩ := b7_kernel_action hsB hB.1 hcontr hK hψ hx hxe
  set T : ℂ → ℂ := fun z => ∫ w in unitDisc, kerK1 F z w * conj (ψ w) with hTdef
  have hnψ1 : normA21 unitDisc ψ ^ 2 = 1 := by
    rw [a21_norm_sq_eq_integral (D := unitDisc) measurableSet_ball hψ, ← hψn.tsum_eq, hxs]
    simp
  have hnψ : normA21 unitDisc ψ ≤ 1 := by
    have : normA21 unitDisc ψ ^ 2 ≤ 1 ^ 2 := by rw [hnψ1]; simp
    exact (ENNReal.pow_le_pow_left_iff two_ne_zero).mp this
  -- the norm of `T ψ`
  set y : ℕ → ℂ := fun m => b7Apply B (fun n => conj (x n)) m with hydef
  have hy := hcontr (fun n => conj (x n)) hxc
  obtain ⟨hT', hTn⟩ := bergman_ell2_series hy.1
  have hTT : EqOn T (fun z => ∑' m, y m * basisE m z) unitDisc := fun z hz => (hTe z hz).tsum_eq.symm
  have hyB : ∀ m, y m = B m 0 := by
    intro m
    simp only [hydef, b7Apply]
    rw [tsum_eq_single 0]
    · simp [hxdef]
    · intro n hn; simp [hxdef, hn]
  have hyS : ∑' m, ‖y m‖ ^ 2 = ∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * ‖a 1 (j + 1)‖ ^ 2 := by
    refine tsum_congr (fun m => ?_)
    rw [hyB, hsB m 0, hB0]
  have hnT1 : normA21 unitDisc T ^ 2 = ENNReal.ofReal (∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * ‖a 1 (j + 1)‖ ^ 2) := by
    rw [normA21_congr_on (U := unitDisc) measurableSet_ball hTT,
      a21_norm_sq_eq_integral (D := unitDisc) measurableSet_ball hT', ← hyS, hTn.tsum_eq]
  have hnT : 1 ≤ normA21 unitDisc T := by
    have h3 : (1 : ℝ≥0∞) ^ 2 ≤ normA21 unitDisc T ^ 2 := by
      rw [hnT1, one_pow]
      simpa using ENNReal.ofReal_le_ofReal hS
    exact (ENNReal.pow_le_pow_left_iff two_ne_zero).mp h3
  exact hnT.trans (le_iSup₂_of_le ψ ⟨hψ, hnψ⟩ le_rfl)



/-- Conjunct 4 of the corrected Remark B.6, for an arbitrary univalent `f₁`. -/
theorem ab6_conj4 {f₁ : ℂ → ℂ} (h₁ : IsUnivalentDisc f₁) (hnull : volume (f₁ '' unitDisc)ᶜ = 0) :
    kerOpNorm (kerK1 f₁) = 1 := by
  refine le_antisymm (kerOpNorm_kerK1_le_one h₁) ?_
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hd0 : deriv f₁ 0 ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball h₁.1 h₁.2 h0
  set α : ℂ := (deriv f₁ 0)⁻¹ with hα
  have hα0 : α ≠ 0 := inv_ne_zero hd0
  set F : ℂ → ℂ := fun u => α * (f₁ u - f₁ 0) with hF
  have hFd : DifferentiableOn ℂ F unitDisc :=
    (differentiableOn_const α).mul (h₁.1.sub_const (f₁ 0))
  have hFi : InjOn F unitDisc := by
    intro z hz w hw he
    apply h₁.2 hz hw
    have : f₁ z - f₁ 0 = f₁ w - f₁ 0 := mul_left_cancel₀ hα0 he
    linear_combination this
  have hF0 : F 0 = 0 := by simp [hF]
  have hfd : ∀ u ∈ unitDisc, HasDerivAt f₁ (deriv f₁ u) u := fun u hu =>
    (h₁.1.differentiableAt (isOpen_ball.mem_nhds hu)).hasDerivAt
  have hFder : ∀ u ∈ unitDisc, deriv F u = α * deriv f₁ u := by
    intro u hu
    exact (((hfd u hu).sub_const (f₁ 0)).const_mul α).deriv
  have hF1 : deriv F 0 = 1 := by
    rw [hFder 0 h0, hα]
    exact inv_mul_cancel₀ hd0
  -- the image of `F` has null complement
  have hnullF : volume (F '' unitDisc)ᶜ = 0 := by
    have hsub : (F '' unitDisc)ᶜ ⊆ (fun y : ℂ => α * (y - f₁ 0)) '' (f₁ '' unitDisc)ᶜ := by
      intro x hx
      refine ⟨x / α + f₁ 0, ?_, by field_simp; ring⟩
      rintro ⟨u, hu, hux⟩
      exact hx ⟨u, hu, by simp only [hF, hux]; field_simp; ring⟩
    refine measure_mono_null hsub ?_
    refine MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_ hnull
    have hAd : Differentiable ℂ (fun y : ℂ => α * (y - f₁ 0)) :=
      (differentiable_const α).mul (differentiable_id.sub_const (f₁ 0))
    exact (hAd.restrictScalars ℝ).differentiableOn
  have hGe := ab6_opNorm_ge hFd hFi hF0 hF1 hnullF
  -- the kernels agree almost everywhere
  have hker : ∀ z ∈ unitDisc, kerK1 F z =ᵐ[volume.restrict unitDisc] kerK1 f₁ z := by
    intro z hz
    filter_upwards [(volume.restrict unitDisc).ae_ne z, ae_restrict_mem (show MeasurableSet unitDisc from measurableSet_ball)]
      with w hwz hw
    rw [kerK1_of_ne F (Ne.symm hwz), kerK1_of_ne f₁ (Ne.symm hwz), hFder z hz, hFder w hw]
    have hfn : f₁ z - f₁ w ≠ 0 := sub_ne_zero.mpr (fun h => hwz (h₁.2 hw hz h.symm))
    simp only [hF]
    have : α * (f₁ z - f₁ 0) - α * (f₁ w - f₁ 0) = α * (f₁ z - f₁ w) := by ring
    rw [this]
    field_simp
  have hnormeq : ∀ ψ : ℂ → ℂ,
      normA21 unitDisc (fun z => ∫ w in unitDisc, kerK1 f₁ z w * conj (ψ w)) =
        normA21 unitDisc (fun z => ∫ w in unitDisc, kerK1 F z w * conj (ψ w)) := by
    intro ψ
    unfold normA21
    congr 1
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem (show MeasurableSet unitDisc from measurableSet_ball)] with z hz
    have he : (∫ w in unitDisc, kerK1 f₁ z w * conj (ψ w)) =
        ∫ w in unitDisc, kerK1 F z w * conj (ψ w) := by
      apply integral_congr_ae
      filter_upwards [hker z hz] with w hw
      rw [hw]
    rw [he]
  have hkeq : kerOpNorm (kerK1 f₁) = kerOpNorm (kerK1 F) := by
    unfold kerOpNorm
    simp only [hnormeq]
  rw [hkeq]
  exact hGe

/-- **Remark B.6** (TT:6206–6236).
- `‖𝒮(f₁) - 𝒮(f₂)‖_∞ ≤ 6 d(f₁, f₂) ≤ 6 ‖K₁(f₁) - K₁(f₂)‖`.
- `‖K₁(f)‖ ≤ 1`, with equality if `ℂ \ f(𝔻)` is a null set.
- Hence `d(f) ≤ 1` [Bra65].

[CORRECTION 2026-10-25] The memoir's converse ("equality iff `ℂ \ f(𝔻)` is null", and "`d(f) = 1` implies that
`ℂ \ f(𝔻)` is null") is false: for `f` mapping onto `ℂ \ {x ≥ 0, |y| ≤ x²}` one has `‖K₁(f)‖ = d(f) = 1` with a
complement of positive area (`collaboration/下属5/REMARK_B6_PROPOSAL.md`). -/
theorem ab6_remark_B_6 {f₁ f₂ : ℂ → ℂ} (h₁ : IsUnivalentDisc f₁) (h₂ : IsUnivalentDisc f₂) :
    (⨆ z ∈ unitDisc, ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ 2 * ‖schwarzianHol f₁ z - schwarzianHol f₂ z‖)) ≤
        6 * brazD f₁ f₂ ∧
      brazD f₁ f₂ ≤ kerOpNorm (fun z w => kerK1 f₁ z w - kerK1 f₂ z w) ∧
      kerOpNorm (kerK1 f₁) ≤ 1 ∧ (volume (f₁ '' unitDisc)ᶜ = 0 → kerOpNorm (kerK1 f₁) = 1) ∧
      brazD f₁ id ≤ 1
:=
  ⟨brazD_schwarzian_bound h₁ h₂, brazD_le_kerOpNorm h₁ h₂, kerOpNorm_kerK1_le_one h₁,
    fun hn => ab6_conj4 h₁ hn, brazD_id_le_one h₁⟩


/-- **Remark B.6** (TT:6206–6236).
- `‖𝒮(f₁) - 𝒮(f₂)‖_∞ ≤ 6 d(f₁, f₂) ≤ 6 ‖K₁(f₁) - K₁(f₂)‖`.
- `‖K₁(f)‖ ≤ 1`, with equality if `ℂ \ f(𝔻)` is a null set.
- Hence `d(f) ≤ 1` [Bra65].

[CORRECTION 2026-10-25] The memoir's converse ("equality iff `ℂ \ f(𝔻)` is null", and "`d(f) = 1` implies that
`ℂ \ f(𝔻)` is null") is false: for `f` mapping onto `ℂ \ {x ≥ 0, |y| ≤ x²}` one has `‖K₁(f)‖ = d(f) = 1` with a
complement of positive area (`collaboration/下属5/REMARK_B6_PROPOSAL.md`). -/
theorem remark_B_6 {f₁ f₂ : ℂ → ℂ} (h₁ : IsUnivalentDisc f₁) (h₂ : IsUnivalentDisc f₂) :
    (⨆ z ∈ unitDisc, ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ 2 * ‖schwarzianHol f₁ z - schwarzianHol f₂ z‖)) ≤
        6 * brazD f₁ f₂ ∧
      brazD f₁ f₂ ≤ kerOpNorm (fun z w => kerK1 f₁ z w - kerK1 f₂ z w) ∧
      kerOpNorm (kerK1 f₁) ≤ 1 ∧ (volume (f₁ '' unitDisc)ᶜ = 0 → kerOpNorm (kerK1 f₁) = 1) ∧
      brazD f₁ id ≤ 1 :=
  ab6_remark_B_6 h₁ h₂

end AppB
end TakhtajanTeo
