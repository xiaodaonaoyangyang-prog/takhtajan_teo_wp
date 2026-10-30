import TakhtajanTeo.Ch1.S8_FiniteDimensional
import TakhtajanTeo.Ch1.WPChangeOfVariables

/-!
# The projector kernel of `Ω^{-1,1}(𝔻, Γ)` (TT:3444–3448)

`pk_projector_kernel` is `projector_kernel` (S8). Route: for fixed `w ∈ 𝔻` the Poincaré series
`Θ(z, w) = Σ_{a ∈ Γ/±1} a'(w)²/(1 - z̄ a(w))⁴` converges absolutely with `(1 - |z|²)² Σ |·| ≤ C(w)` uniformly in `z`
(sub-mean value + bounded overlap of the translates of a small disc), so `K_w = (12/π) ρ⁻¹ ρ(w)⁻¹ Θ(·, w)` is in
`Ω^{-1,1}(𝔻, Γ)`; unfolding over the fundamental domain and the Bergman reproduction give `(K_w, b)_Γ = \overline{b(w)}`,
and the orthonormal expansion of `K_w` is the statement.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

theorem pk_fund {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) :
    IsFundDomainD Γ (fundDomainOn Γ unitDisc) := by
  have hex : ∃ F, IsFundDomainOn Γ unitDisc F :=
    ⟨_, fdr_isFundDomainD_refl hΓ (isFundDomain_fundDomain hΓ)⟩
  have h := hex.choose_spec
  unfold fundDomainOn
  rw [dif_pos hex]
  exact h

theorem pk_cocycle {g : SL2C} (hg : IsSU11 g) {z v : ℂ} (hz : z ∈ unitDisc) (hv : v ∈ unitDisc) :
    (1 - conj (mob g z) * mob g v) * (conj (g 1 0 * z + g 1 1) * (g 1 0 * v + g 1 1)) = 1 - conj z * v := by
  have hcz : g 1 0 * z + g 1 1 ≠ 0 := fdD_denom_ne hg (mem_ball_zero_iff.mp hz)
  have hcv : g 1 0 * v + g 1 1 ≠ 0 := fdD_denom_ne hg (mem_ball_zero_iff.mp hv)
  have hcz' : conj (g 1 0 * z + g 1 1) ≠ 0 := (map_ne_zero _).mpr hcz
  have hdet := fd_det g
  have e1 : conj (mob g z) * mob g v * (conj (g 1 0 * z + g 1 1) * (g 1 0 * v + g 1 1)) =
      conj (g 0 0 * z + g 0 1) * (g 0 0 * v + g 0 1) := by
    have hcz'' : conj (z * g 1 0 + g 1 1) ≠ 0 := by rwa [mul_comm z]
    unfold mob
    rw [map_div₀]
    field_simp
  obtain ⟨h1, h2⟩ := hg
  rw [sub_mul, one_mul, e1, h1, h2]
  rw [h1, h2] at hdet
  simp only [map_add, map_mul, Complex.conj_conj]
  linear_combination (1 - conj z * v) * hdet

theorem pk_deriv_mob (g : SL2C) {z : ℂ} (hD : g 1 0 * z + g 1 1 ≠ 0) :
    deriv (mob g) z = ((g 1 0 * z + g 1 1) ^ 2)⁻¹ := by
  rw [(wp_mob_hasDerivAt g hD).deriv, one_div]

theorem pk_left_perm {Γ : Subgroup SL2C} {δ : SL2C} (hδ : δ ∈ Γ) :
    ∃ e : ((fun g : SL2C => mob g) '' (Γ : Set SL2C)) ≃ ((fun g : SL2C => mob g) '' (Γ : Set SL2C)),
      ∀ a : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)), ∃ g ∈ Γ, (a : ℂ → ℂ) = mob g ∧
        ((e a : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C))) : ℂ → ℂ) = mob (δ * g) := by
  classical
  set A := (fun g : SL2C => mob g) '' (Γ : Set SL2C) with hA
  let rep : A → SL2C := fun b => Classical.choose b.2
  have hrep : ∀ b : A, rep b ∈ Γ ∧ mob (rep b) = b.1 := fun b => Classical.choose_spec b.2
  have key : ∀ (k : SL2C) (b : A), (b : ℂ → ℂ) = mob (rep b) → ∀ x : SL2C, mob x = b.1 →
      mob (k * x) = mob (k * rep b) := by
    intro k b _ x hx
    have h1 : mob (rep b) = mob x := by rw [hx]; exact (hrep b).2
    rcases fd_mob_eq h1 with h | h
    · rw [h]
    · rw [h, mul_neg, fd_mob_neg]
  let f : SL2C → A → A := fun k b => if hk : k ∈ Γ then ⟨mob (k * rep b), k * rep b, Γ.mul_mem hk (hrep b).1, rfl⟩
    else b
  have hf : ∀ k ∈ Γ, ∀ b, ((f k b : A) : ℂ → ℂ) = mob (k * rep b) := fun k hk b => by
    simp only [f, dif_pos hk]
  have hcomp : ∀ k ∈ Γ, ∀ l ∈ Γ, ∀ b, f k (f l b) = f (k * l) b := by
    intro k hk l hl b
    apply Subtype.ext
    rw [hf k hk, hf (k * l) (Γ.mul_mem hk hl), mul_assoc]
    exact (key k (f l b) (hrep _).2.symm (l * rep b) (hf l hl b).symm).symm
  have hone : ∀ b, f 1 b = b := fun b => by
    apply Subtype.ext
    rw [hf 1 Γ.one_mem, one_mul]; exact (hrep b).2
  refine ⟨⟨f δ, f δ⁻¹, fun b => ?_, fun b => ?_⟩, fun b => ⟨rep b, (hrep b).1, (hrep b).2.symm, hf δ hδ b⟩⟩
  · rw [hcomp _ (Γ.inv_mem hδ) _ hδ, inv_mul_cancel, hone]
  · rw [hcomp _ hδ _ (Γ.inv_mem hδ), mul_inv_cancel, hone]

theorem pk_one_sub_ne {a b : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) : 1 - a * b ≠ 0 := by
  intro h0
  have h1 : a * b = 1 := (sub_eq_zero.mp h0).symm
  have h2 : ‖a * b‖ < 1 := by
    rw [norm_mul]; nlinarith [norm_nonneg a, norm_nonneg b]
  rw [h1, norm_one] at h2
  exact lt_irrefl _ h2

/-- `c_g(g⁻¹ z) · c_{g⁻¹}(z) = 1`. -/
theorem pk_denom_inv {g : SL2C} {z : ℂ} (hD : (g⁻¹ : SL2C) 1 0 * z + (g⁻¹ : SL2C) 1 1 ≠ 0)
    (hD' : g 1 0 * mob g⁻¹ z + g 1 1 ≠ 0) :
    (g 1 0 * mob g⁻¹ z + g 1 1) * ((g⁻¹ : SL2C) 1 0 * z + (g⁻¹ : SL2C) 1 1) = 1 := by
  have h := (fd_mob_mul hD hD').1
  rw [mul_inv_cancel] at h
  rw [← h]
  simp

theorem pk_near_finite {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {r : ℝ} (hr : r < 1) :
    {a : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)) |
      ∃ u : ℂ, ‖u‖ ≤ r ∧ ‖(a : ℂ → ℂ) u‖ ≤ r}.Finite := by
  haveI : DiscreteTopology Γ := hΓ.2
  set C : ℝ := 1 + 1 / ((1 - r) ^ 2 * (1 - r ^ 2)) with hC
  have hbound : ∀ g : SL2C, IsSU11 g → ∀ u : ℂ, ‖u‖ ≤ r → ‖mob g u‖ ≤ r →
      ∀ i j, ‖(g : Matrix (Fin 2) (Fin 2) ℂ) i j‖ ≤ C := by
    intro g hg u hu hgu
    have hr0 : 0 ≤ r := (norm_nonneg u).trans hu
    have hu1 : ‖u‖ < 1 := lt_of_le_of_lt hu hr
    have hD := fdD_denom_ne hg hu1
    have hid := fd_su11_identity hg u
    have hdet := fd_su11_det hg
    set c := g 1 0 * u + g 1 1 with hc
    have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hD
    have hN : ‖g 0 0 * u + g 0 1‖ ≤ r * ‖c‖ := by
      have : mob g u = (g 0 0 * u + g 0 1) / c := rfl
      rw [this, norm_div, div_le_iff₀ hcpos] at hgu
      exact hgu
    -- `‖c‖² (1 - r²) ≤ 1`
    have hc2 : ‖c‖ ^ 2 * (1 - r ^ 2) ≤ 1 := by
      have h1 : ‖g 0 0 * u + g 0 1‖ ^ 2 ≤ r ^ 2 * ‖c‖ ^ 2 := by
        have := mul_self_le_mul_self (norm_nonneg _) hN
        nlinarith
      nlinarith [norm_nonneg u, sq_nonneg ‖u‖]
    -- `‖g 0 1‖ ≤ ‖g 0 0‖`, `‖c‖ ≥ ‖g 0 0‖ (1 - r)`
    have hb : ‖g 0 1‖ ≤ ‖g 0 0‖ := by
      have : ‖g 0 1‖ ^ 2 ≤ ‖g 0 0‖ ^ 2 := by linarith
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp this
    have hcl : ‖g 0 0‖ * (1 - r) ≤ ‖c‖ := by
      have e : c = conj (g 0 1) * u + conj (g 0 0) := by rw [hc, hg.1, hg.2]
      have h1 : ‖conj (g 0 0)‖ - ‖conj (g 0 1) * u‖ ≤ ‖c‖ := by
        rw [e, add_comm]; exact norm_sub_le_norm_add _ _
      rw [Complex.norm_conj, norm_mul, Complex.norm_conj] at h1
      nlinarith [norm_nonneg (g 0 1), norm_nonneg u, norm_nonneg (g 0 0)]
    have hpos : 0 < (1 - r) ^ 2 * (1 - r ^ 2) := by
      have : 0 < 1 - r := by linarith
      have : 0 < 1 - r ^ 2 := by nlinarith
      positivity
    have ha2 : ‖g 0 0‖ ^ 2 ≤ 1 / ((1 - r) ^ 2 * (1 - r ^ 2)) := by
      rw [le_div_iff₀ hpos]
      have h1 : (‖g 0 0‖ * (1 - r)) ^ 2 ≤ ‖c‖ ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (by linarith)) hcl 2
      have h2 : 0 ≤ 1 - r ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right h1 h2]
    have ha : ‖g 0 0‖ ≤ C := by
      rw [hC]
      by_cases h : ‖g 0 0‖ ≤ 1
      · have : 0 ≤ 1 / ((1 - r) ^ 2 * (1 - r ^ 2)) := by positivity
        linarith
      · push_neg at h
        nlinarith
    intro i j
    fin_cases i <;> fin_cases j
    · exact ha
    · exact hb.trans ha
    · show ‖g 1 0‖ ≤ C
      rw [hg.1, Complex.norm_conj]; exact hb.trans ha
    · show ‖g 1 1‖ ≤ C
      rw [hg.2, Complex.norm_conj]; exact ha
  refine Set.Finite.of_finite_image (f := Subtype.val) ?_ Subtype.val_injective.injOn
  refine ((fd_bounded_finite (Γ := Γ) C).image (fun g : SL2C => mob g)).subset ?_
  rintro _ ⟨⟨_, g, hg, rfl⟩, ⟨u, hu, hau⟩, rfl⟩
  exact ⟨g, ⟨hg, hbound g (hΓ.1 g hg) u hu hau⟩, rfl⟩

/-- Per-action mean-value estimate. -/
theorem pk_mv_one {g : SL2C} (hg : IsSU11 g) {z w : ℂ} (hz : z ∈ unitDisc) {s : ℝ} (hs : 0 < s)
    (hB : ball w s ⊆ unitDisc) :
    ENNReal.ofReal (π * s ^ 2 / 3) *
        ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ 2 * ‖deriv (mob g) w ^ 2 / (1 - conj z * mob g w) ^ 4‖) ≤
      ∫⁻ x in mob g '' ball w s, ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ 2 * ‖(1 - x * conj z) ^ 4‖⁻¹) := by
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hw : w ∈ unitDisc := hB (mem_ball_self hs)
  set f : ℂ → ℝ≥0∞ := fun x => ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ 2 * ‖(1 - x * conj z) ^ 4‖⁻¹) with hf
  set H : ℂ → ℂ := fun u => ((g 1 0 * u + g 1 1) ^ 2)⁻¹ * ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) / (1 - mob g u * conj z) ^ 2
    with hH
  have hden : ∀ u ∈ unitDisc, 1 - mob g u * conj z ≠ 0 := by
    intro u hu h0
    have hm : ‖mob g u‖ < 1 := fdD_mob_lt hg (mem_ball_zero_iff.mp hu)
    have h1 : mob g u * conj z = 1 := (sub_eq_zero.mp h0).symm
    have h2 : ‖mob g u * conj z‖ < 1 := by
      rw [norm_mul, Complex.norm_conj]
      nlinarith [norm_nonneg (mob g u), norm_nonneg z]
    rw [h1, norm_one] at h2
    exact lt_irrefl _ h2
  have hHd : ∀ u ∈ unitDisc, DifferentiableAt ℂ H u := by
    intro u hu
    have hc := fdD_denom_ne hg (mem_ball_zero_iff.mp hu)
    have hm := fd_mob_differentiableAt g hc
    refine DifferentiableAt.div ?_ ?_ (pow_ne_zero 2 (hden u hu))
    · exact ((((differentiableAt_id.const_mul (g 1 0)).add_const (g 1 1)).pow 2).inv
        (pow_ne_zero 2 hc)).mul_const _
    · exact (differentiableAt_const _).sub (hm.mul_const _) |>.pow 2
  -- pointwise norm identities
  have hnorm : ∀ u ∈ unitDisc, ENNReal.ofReal (‖H u‖ ^ 2) =
      ENNReal.ofReal (‖deriv (mob g) u‖ ^ 2) * f (mob g u) := by
    intro u hu
    have hc := fdD_denom_ne hg (mem_ball_zero_iff.mp hu)
    rw [hf, ← ENNReal.ofReal_mul (sq_nonneg _), pk_deriv_mob g hc]
    congr 1
    have hd := hden u hu
    have hcn : ‖g 1 0 * u + g 1 1‖ ≠ 0 := norm_ne_zero_iff.mpr hc
    have hdn : ‖1 - mob g u * conj z‖ ≠ 0 := norm_ne_zero_iff.mpr hd
    have h1z : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
    simp only [hH, norm_div, norm_mul, norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg h1z]
    field_simp
  have hcw := fdD_denom_ne hg (mem_ball_zero_iff.mp hw)
  have hHw : ‖H w‖ ^ 2 = (1 - ‖z‖ ^ 2) ^ 2 * ‖deriv (mob g) w ^ 2 / (1 - conj z * mob g w) ^ 4‖ := by
    rw [pk_deriv_mob g hcw]
    have h1z : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
    have hd := hden w hw
    have hcn : ‖g 1 0 * w + g 1 1‖ ≠ 0 := norm_ne_zero_iff.mpr hcw
    have hdn : ‖1 - mob g w * conj z‖ ≠ 0 := norm_ne_zero_iff.mpr hd
    rw [mul_comm (conj z) (mob g w)]
    simp only [hH, norm_div, norm_mul, norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg h1z]
    field_simp
  -- mean value on the translated disc
  set F : ℂ → ℂ := fun ζ => H (w + ζ) with hF
  have hFd : DifferentiableOn ℂ F (ball (0 : ℂ) s) := by
    intro ζ hζ
    have hwz : w + ζ ∈ ball w s := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left]; simpa using hζ
    exact ((hHd _ (hB hwz)).comp ζ ((differentiableAt_const w).add differentiableAt_id)).differentiableWithinAt
  have hmv := WPCV.wpcv_mean_value_sq hs hFd
  have hsq : ∀ x : ℂ, (‖x‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (‖x‖ ^ 2) := fun x => by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, enorm_eq_nnnorm]
  have htr : ∫⁻ ζ in ball (0 : ℂ) s, (‖F ζ‖₊ : ℝ≥0∞) ^ 2 = ∫⁻ u in ball w s, (‖H u‖₊ : ℝ≥0∞) ^ 2 := by
    have hpre : (fun ζ : ℂ => w + ζ) ⁻¹' ball w s = ball (0 : ℂ) s := by
      ext ζ; simp [mem_ball, dist_eq_norm]
    rw [← hpre]
    exact (measurePreserving_add_left volume w).setLIntegral_comp_preimage_emb
      (measurableEmbedding_addLeft w) (fun u => (‖H u‖₊ : ℝ≥0∞) ^ 2) (ball w s)
  -- change of variables
  have hgen : ∀ u ∈ ball w s, g 1 0 * u + g 1 1 ≠ 0 := fun u hu =>
    fdD_denom_ne hg (mem_ball_zero_iff.mp (hB hu))
  have hinj : InjOn (mob g) (ball w s) := by
    intro u1 h1 u2 h2 h
    rw [← (fd_inv_step g (hgen u1 h1)).2, ← (fd_inv_step g (hgen u2 h2)).2, h]
  rw [fd_lintegral_image g measurableSet_ball hgen hinj f]
  calc ENNReal.ofReal (π * s ^ 2 / 3) *
        ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ 2 * ‖deriv (mob g) w ^ 2 / (1 - conj z * mob g w) ^ 4‖)
      = ENNReal.ofReal (π * s ^ 2 / 3) * (‖F 0‖₊ : ℝ≥0∞) ^ 2 := by
        rw [hsq, ← hHw]; simp [hF]
    _ ≤ ∫⁻ ζ in ball (0 : ℂ) s, (‖F ζ‖₊ : ℝ≥0∞) ^ 2 := hmv
    _ = ∫⁻ u in ball w s, ENNReal.ofReal (‖deriv (mob g) u‖ ^ 2) * f (mob g u) := by
        rw [htr]
        refine setLIntegral_congr_fun measurableSet_ball fun u hu => ?_
        rw [hsq, hnorm u (hB hu)]

/-- Bounded overlap: a point lies in at most `m` translates `a(B)`, `B = B(w, s)` inside `|u| ≤ R`. -/
theorem pk_overlap {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {w : ℂ} {s R : ℝ} (hR : R < 1)
    (hB : ∀ u ∈ ball w s, ‖u‖ ≤ R) (S : Finset ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C))) (ζ : ℂ) :
    (S.filter fun a : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)) => ζ ∈ (a : ℂ → ℂ) '' ball w s).card ≤ (pk_near_finite hΓ hR).toFinset.card := by
  classical
  rcases (S.filter fun a : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)) => ζ ∈ (a : ℂ → ℂ) '' ball w s).eq_empty_or_nonempty with h | ⟨a0, ha0⟩
  · rw [h]; exact Nat.zero_le _
  let rep : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)) → SL2C := fun b => Classical.choose b.2
  have hrep : ∀ b : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)), rep b ∈ Γ ∧ mob (rep b) = b.1 := fun b => Classical.choose_spec b.2
  have hu1 : ∀ u ∈ ball w s, ‖u‖ < 1 := fun u hu => lt_of_le_of_lt (hB u hu) hR
  obtain ⟨u0, hu0, hζ0⟩ := (Finset.mem_filter.mp ha0).2
  set g0 := rep a0 with hg0
  have hg0Γ : g0 ∈ Γ := (hrep a0).1
  have hg0su := hΓ.1 g0 hg0Γ
  have hζ0' : mob g0 u0 = ζ := by rw [hg0, (hrep a0).2]; exact hζ0
  let φ : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)) → ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)) := fun b => ⟨mob (g0⁻¹ * rep b), g0⁻¹ * rep b, Γ.mul_mem (Γ.inv_mem hg0Γ) (hrep b).1, rfl⟩
  have hφ : ∀ b ∈ S.filter (fun a : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)) => ζ ∈ (a : ℂ → ℂ) '' ball w s), φ b ∈ (pk_near_finite hΓ hR).toFinset := by
    intro b hb
    obtain ⟨u, hu, hζ⟩ := (Finset.mem_filter.mp hb).2
    rw [Set.Finite.mem_toFinset]
    refine ⟨u, hB u hu, ?_⟩
    have hsu := hΓ.1 _ (hrep b).1
    have hD : rep b 1 0 * u + rep b 1 1 ≠ 0 := fdD_denom_ne hsu (hu1 u hu)
    have hζb : mob (rep b) u = ζ := by rw [(hrep b).2]; exact hζ
    have hζd : ‖ζ‖ < 1 := by rw [← hζb]; exact fdD_mob_lt hsu (hu1 u hu)
    have hD2 : (g0⁻¹ : SL2C) 1 0 * mob (rep b) u + (g0⁻¹ : SL2C) 1 1 ≠ 0 := by
      rw [hζb]; exact fdD_denom_ne (isSU11_inv hg0su) hζd
    show ‖mob (g0⁻¹ * rep b) u‖ ≤ R
    rw [(fd_mob_mul hD hD2).2, hζb, ← hζ0', (fd_inv_step g0 (fdD_denom_ne hg0su (hu1 u0 hu0))).2]
    exact hB u0 hu0
  have hinj : Set.InjOn φ (S.filter (fun a : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)) => ζ ∈ (a : ℂ → ℂ) '' ball w s)) := by
    intro b1 _ b2 _ h
    have h' : mob (g0⁻¹ * rep b1) = mob (g0⁻¹ * rep b2) := congrArg Subtype.val h
    apply Subtype.ext
    rw [← (hrep b1).2, ← (hrep b2).2]
    rcases fd_mob_eq h' with e | e
    · rw [mul_left_cancel e]
    · have : g0⁻¹ * rep b2 = g0⁻¹ * -rep b1 := by rw [e, mul_neg]
      rw [mul_left_cancel this, fd_mob_neg]
  exact Finset.card_le_card_of_injOn φ hφ hinj

theorem pk_packing {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {w : ℂ} (hw : w ∈ unitDisc) :
    ∃ C : ℝ, ∀ z ∈ unitDisc, ∀ S : Finset ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)),
      (1 - ‖z‖ ^ 2) ^ 2 * ∑ a ∈ S, ‖deriv (a : ℂ → ℂ) w ^ 2 / (1 - conj z * (a : ℂ → ℂ) w) ^ 4‖ ≤ C := by
  classical
  have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
  set s : ℝ := (1 - ‖w‖) / 2 with hsdef
  set R : ℝ := (1 + ‖w‖) / 2 with hRdef
  have hs : 0 < s := by rw [hsdef]; linarith
  have hR : R < 1 := by rw [hRdef]; linarith
  have hBR : ∀ u ∈ ball w s, ‖u‖ ≤ R := by
    intro u hu
    have h1 : ‖u - w‖ < s := by rw [← dist_eq_norm]; exact hu
    have h2 : ‖u‖ ≤ ‖w‖ + ‖u - w‖ := by
      calc ‖u‖ = ‖w + (u - w)‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    rw [hRdef]; rw [hsdef] at h1; linarith
  have hB : ball w s ⊆ unitDisc := fun u hu => mem_ball_zero_iff.mpr (lt_of_le_of_lt (hBR u hu) hR)
  set m : ℕ := (pk_near_finite hΓ hR).toFinset.card with hm
  refine ⟨3 * m / s ^ 2, fun z hz S => ?_⟩
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  set f : ℂ → ℝ≥0∞ := fun x => ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ 2 * ‖(1 - x * conj z) ^ 4‖⁻¹) with hf
  have hfm : Measurable f := by
    rw [hf]; fun_prop
  set t : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)) → ℝ := fun a =>
    (1 - ‖z‖ ^ 2) ^ 2 * ‖deriv (a : ℂ → ℂ) w ^ 2 / (1 - conj z * (a : ℂ → ℂ) w) ^ 4‖ with ht
  have ht0 : ∀ a, 0 ≤ t a := fun a => mul_nonneg (sq_nonneg _) (norm_nonneg _)
  set E : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)) → Set ℂ := fun a => (a : ℂ → ℂ) '' ball w s
    with hE
  have hEm : ∀ a, MeasurableSet (E a) := by
    rintro ⟨_, g, hg, rfl⟩
    have hgen : ∀ u ∈ ball w s, g 1 0 * u + g 1 1 ≠ 0 := fun u hu =>
      fdD_denom_ne (hΓ.1 g hg) (mem_ball_zero_iff.mp (hB hu))
    refine measurableSet_ball.image_of_continuousOn_injOn
      (fun u hu => (fd_mob_differentiableAt g (hgen u hu)).continuousAt.continuousWithinAt) ?_
    intro u1 h1 u2 h2 h
    have h' : mob g u1 = mob g u2 := h
    rw [← (fd_inv_step g (hgen u1 h1)).2, ← (fd_inv_step g (hgen u2 h2)).2, h']
  have hEsub : ∀ a, E a ⊆ unitDisc := by
    rintro ⟨_, g, hg, rfl⟩ _ ⟨u, hu, rfl⟩
    exact mem_ball_zero_iff.mpr (fdD_mob_lt (hΓ.1 g hg) (mem_ball_zero_iff.mp (hB hu)))
  have hone : ∀ a, ENNReal.ofReal (π * s ^ 2 / 3) * ENNReal.ofReal (t a) ≤ ∫⁻ x in E a, f x := by
    rintro ⟨_, g, hg, rfl⟩
    exact pk_mv_one (hΓ.1 g hg) hz hs hB
  have hfD : ∫⁻ x in unitDisc, f x = ENNReal.ofReal π := by
    have hint := (proj_kernel_integrableOn hz1).const_mul ((1 - ‖z‖ ^ 2) ^ 2)
    rw [hf, ← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun x => mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (norm_nonneg _))),
      integral_const_mul, proj_kernel_integral hz1]
    have : (1 - ‖z‖ ^ 2) ^ 2 ≠ 0 := by
      have : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
      positivity
    have h1 : (1 - ‖z‖ ^ 2) ≠ 0 := by nlinarith [norm_nonneg z]
    congr 1
    field_simp
  have hpt : ∀ x, ∑ a ∈ S, (E a).indicator f x ≤ (m : ℝ≥0∞) * unitDisc.indicator f x := by
    intro x
    rw [Finset.sum_indicator_eq_sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
    by_cases hx : x ∈ unitDisc
    · rw [indicator_of_mem hx]
      gcongr
      exact_mod_cast pk_overlap hΓ hR hBR S x
    · have : S.filter (fun a => x ∈ E a) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro a _ hxa
        exact hx (hEsub a hxa)
      rw [this]; simp
  have hsum : ∑ a ∈ S, ∫⁻ x in E a, f x ≤ (m : ℝ≥0∞) * ENNReal.ofReal π := by
    calc ∑ a ∈ S, ∫⁻ x in E a, f x = ∑ a ∈ S, ∫⁻ x, (E a).indicator f x := by
          refine Finset.sum_congr rfl fun a _ => (lintegral_indicator (hEm a) f).symm
      _ = ∫⁻ x, ∑ a ∈ S, (E a).indicator f x :=
          (lintegral_finsetSum S fun a _ => hfm.indicator (hEm a)).symm
      _ ≤ ∫⁻ x, (m : ℝ≥0∞) * unitDisc.indicator f x := lintegral_mono hpt
      _ = (m : ℝ≥0∞) * ENNReal.ofReal π := by
          rw [lintegral_const_mul _ (hfm.indicator (show MeasurableSet unitDisc from measurableSet_ball)),
            lintegral_indicator (show MeasurableSet unitDisc from measurableSet_ball) f, hfD]
  have hmain : ENNReal.ofReal (π * s ^ 2 / 3) * ENNReal.ofReal (∑ a ∈ S, t a) ≤
      ENNReal.ofReal (m * π) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun a _ => ht0 a, Finset.mul_sum, ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ENNReal.ofReal_natCast]
    exact (Finset.sum_le_sum fun a _ => hone a).trans hsum
  have hpos : 0 < π * s ^ 2 / 3 := by positivity
  rw [← ENNReal.ofReal_mul hpos.le,
    ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Nat.cast_nonneg m) Real.pi_pos.le)] at hmain
  have key : (∑ a ∈ S, t a) * s ^ 2 ≤ 3 * m := by
    by_contra hc'
    have hc := not_le.mp hc'
    have := mul_lt_mul_of_pos_left hc Real.pi_pos
    nlinarith
  rw [Finset.mul_sum, le_div_iff₀ (by positivity)]
  exact key

/-- The packing bound for the full series. -/
theorem pk_tsum_bound {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {w : ℂ} (hw : w ∈ unitDisc) :
    ∃ C : ℝ, ∀ z ∈ unitDisc,
      Summable (fun a : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)) =>
        ‖deriv (a : ℂ → ℂ) w ^ 2 / (1 - conj z * (a : ℂ → ℂ) w) ^ 4‖) ∧
      (1 - ‖z‖ ^ 2) ^ 2 * ∑' a : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)),
        ‖deriv (a : ℂ → ℂ) w ^ 2 / (1 - conj z * (a : ℂ → ℂ) w) ^ 4‖ ≤ C := by
  obtain ⟨C, hC⟩ := pk_packing hΓ hw
  refine ⟨C, fun z hz => ?_⟩
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hp : 0 < (1 - ‖z‖ ^ 2) ^ 2 := by
    have : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
    positivity
  have hS : ∀ S : Finset ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)),
      ∑ a ∈ S, ‖deriv (a : ℂ → ℂ) w ^ 2 / (1 - conj z * (a : ℂ → ℂ) w) ^ 4‖ ≤ C / (1 - ‖z‖ ^ 2) ^ 2 :=
    fun S => by rw [le_div_iff₀ hp, mul_comm]; exact hC z hz S
  have h0 : 0 ≤ fun a : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)) =>
      ‖deriv (a : ℂ → ℂ) w ^ 2 / (1 - conj z * (a : ℂ → ℂ) w) ^ 4‖ := fun a => norm_nonneg _
  refine ⟨summable_of_sum_le h0 hS, ?_⟩
  have := Real.tsum_le_of_sum_le h0 hS
  rw [le_div_iff₀ hp, mul_comm] at this
  exact this

theorem pk_summable {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {z w : ℂ} (hz : z ∈ unitDisc) (hw : w ∈ unitDisc) :
    Summable fun a : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)) =>
      ‖deriv (a : ℂ → ℂ) w ^ 2 / (1 - conj z * (a : ℂ → ℂ) w) ^ 4‖ := by
  obtain ⟨C, hC⟩ := pk_tsum_bound hΓ hw
  exact (hC z hz).1

theorem pk_theta_diff {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {w : ℂ} (hw : w ∈ unitDisc) :
    DifferentiableOn ℂ (fun z => conj (∑' a : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)),
      deriv (a : ℂ → ℂ) w ^ 2 / (1 - conj z * (a : ℂ → ℂ) w) ^ 4)) unitDisc := by
  have h0 := pk_summable hΓ (z := 0) (by simp [unitDisc]) hw
  simp only [map_zero, zero_mul, sub_zero, one_pow, div_one] at h0
  have hconj : (fun z => conj (∑' a : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)),
      deriv (a : ℂ → ℂ) w ^ 2 / (1 - conj z * (a : ℂ → ℂ) w) ^ 4)) =
      fun z => ∑' a : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)),
        conj (deriv (a : ℂ → ℂ) w) ^ 2 / (1 - z * conj ((a : ℂ → ℂ) w)) ^ 4 := by
    funext z
    rw [Complex.conj_tsum]
    congr 1; funext a
    simp [map_div₀, map_pow, map_sub, map_mul]
  rw [hconj]
  intro z hz
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  set r : ℝ := (1 + ‖z‖) / 2 with hr
  have hr1 : r < 1 := by rw [hr]; linarith
  have hzr : z ∈ ball (0 : ℂ) r := mem_ball_zero_iff.mpr (by rw [hr]; linarith)
  have hr0 : 0 < 1 - r := by linarith
  have hD : DifferentiableOn ℂ (fun z => ∑' a : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)),
      conj (deriv (a : ℂ → ℂ) w) ^ 2 / (1 - z * conj ((a : ℂ → ℂ) w)) ^ 4) (ball (0 : ℂ) r) := by
    refine differentiableOn_tsum_of_summable_norm (h0.div_const ((1 - r) ^ 4)) ?_ isOpen_ball ?_
    · intro a u hu
      have hu1 : ‖u‖ < 1 := lt_trans (mem_ball_zero_iff.mp hu) hr1
      have haw : ‖(a : ℂ → ℂ) w‖ < 1 := mem_ball_zero_iff.mp (fdD_action_mem hΓ a hw)
      have hne : 1 - u * conj ((a : ℂ → ℂ) w) ≠ 0 := by
        intro h0
        have h1 : u * conj ((a : ℂ → ℂ) w) = 1 := (sub_eq_zero.mp h0).symm
        have h2 : ‖u * conj ((a : ℂ → ℂ) w)‖ < 1 := by
          rw [norm_mul, Complex.norm_conj]
          nlinarith [norm_nonneg u, norm_nonneg ((a : ℂ → ℂ) w)]
        rw [h1, norm_one] at h2; exact lt_irrefl _ h2
      have hd1 : DifferentiableAt ℂ (fun u : ℂ => (1 - u * conj ((a : ℂ → ℂ) w)) ^ 4) u :=
        ((differentiableAt_const (1 : ℂ)).sub (differentiableAt_id.mul_const _)).pow 4
      exact ((differentiableAt_const (conj (deriv (a : ℂ → ℂ) w) ^ 2)).div hd1
        (pow_ne_zero 4 hne)).differentiableWithinAt
    · intro a u hu
      have hu1 : ‖u‖ < r := mem_ball_zero_iff.mp hu
      have haw : ‖(a : ℂ → ℂ) w‖ < 1 := mem_ball_zero_iff.mp (fdD_action_mem hΓ a hw)
      have hlow : 1 - r ≤ ‖1 - u * conj ((a : ℂ → ℂ) w)‖ := by
        have h1 : ‖u * conj ((a : ℂ → ℂ) w)‖ ≤ r := by
          rw [norm_mul, Complex.norm_conj]
          nlinarith [norm_nonneg u, norm_nonneg ((a : ℂ → ℂ) w)]
        have h2 := norm_sub_norm_le (1 : ℂ) (u * conj ((a : ℂ → ℂ) w))
        rw [norm_one] at h2
        linarith
      rw [norm_div, norm_pow, norm_pow, Complex.norm_conj, norm_pow]
      exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
        (pow_le_pow_left₀ hr0.le hlow 4)
  exact (hD.differentiableAt (isOpen_ball.mem_nhds hzr)).differentiableWithinAt

theorem pk_theta_inv {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {δ : SL2C} (hδ : δ ∈ Γ) {z w : ℂ}
    (hz : z ∈ unitDisc) (hw : w ∈ unitDisc) :
    (∑' a : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)),
        deriv (a : ℂ → ℂ) w ^ 2 / (1 - conj (mob δ z) * (a : ℂ → ℂ) w) ^ 4) * conj (deriv (mob δ) z) ^ 2 =
      ∑' a : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)),
        deriv (a : ℂ → ℂ) w ^ 2 / (1 - conj z * (a : ℂ → ℂ) w) ^ 4 := by
  obtain ⟨e, he⟩ := pk_left_perm (Γ.inv_mem hδ)
  rw [← e.tsum_eq (fun a : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)) =>
    deriv (a : ℂ → ℂ) w ^ 2 / (1 - conj z * (a : ℂ → ℂ) w) ^ 4), ← tsum_mul_right]
  refine tsum_congr fun a => ?_
  obtain ⟨g, hg, ha, hea⟩ := he a
  rw [ha, hea]
  have hsu := hΓ.1 g hg
  have hsd := hΓ.1 δ hδ
  have hsdi := isSU11_inv hsd
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
  have hcw : g 1 0 * w + g 1 1 ≠ 0 := fdD_denom_ne hsu hw1
  set v := mob g w with hv
  have hv1 : ‖v‖ < 1 := fdD_mob_lt hsu hw1
  have hp : (δ⁻¹ : SL2C) 1 0 * v + (δ⁻¹ : SL2C) 1 1 ≠ 0 := fdD_denom_ne hsdi hv1
  obtain ⟨hcv', hback⟩ := fd_inv_step δ⁻¹ hp
  rw [inv_inv] at hcv' hback
  set v' := mob δ⁻¹ v with hv'
  have hv'1 : ‖v'‖ < 1 := fdD_mob_lt hsdi hv1
  have hmul := fd_mob_mul (g := δ⁻¹) hcw hp
  rw [← hv'] at hmul
  have hcz : δ 1 0 * z + δ 1 1 ≠ 0 := fdD_denom_ne hsd hz1
  have hcoc := pk_cocycle hsd hz (mem_ball_zero_iff.mpr hv'1)
  rw [hback] at hcoc
  have hpq : (δ⁻¹ : SL2C) 1 0 * v + (δ⁻¹ : SL2C) 1 1 = (δ 1 0 * v' + δ 1 1)⁻¹ := by
    have hg' : (δ⁻¹ : SL2C) 1 0 * mob δ v' + (δ⁻¹ : SL2C) 1 1 ≠ 0 := by rw [hback]; exact hp
    have h := (fd_mob_mul hcv' hg').1
    rw [inv_mul_cancel, hback] at h
    exact eq_inv_of_mul_eq_one_left (by rw [← h]; simp)
  have hmz : ‖mob δ z‖ < 1 := fdD_mob_lt hsd hz1
  have hY : 1 - conj (mob δ z) * v ≠ 0 := pk_one_sub_ne (by rwa [Complex.norm_conj]) hv1
  have hD2 : (δ⁻¹ * g : SL2C) 1 0 * w + (δ⁻¹ * g : SL2C) 1 1 ≠ 0 := by
    rw [hmul.1]; exact mul_ne_zero hp hcw
  rw [pk_deriv_mob g hcw, pk_deriv_mob δ hcz, pk_deriv_mob _ hD2, hmul.1, hmul.2, ← hcoc, hpq]
  have hczc : conj (δ 1 0 * z + δ 1 1) ≠ 0 := (map_ne_zero _).mpr hcz
  simp only [map_inv₀, map_pow]
  field_simp

theorem pk_K_harmonic {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {w : ℂ} (hw : w ∈ unitDisc) :
    IsHarmonicD fun z => 12 / π * (rho z : ℂ)⁻¹ * (rho w : ℂ)⁻¹ *
      ∑' a : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)),
        deriv (a : ℂ → ℂ) w ^ 2 / (1 - conj z * (a : ℂ → ℂ) w) ^ 4 := by
  obtain ⟨C, hC⟩ := pk_tsum_bound hΓ hw
  set Θ : ℂ → ℂ := fun z => ∑' a : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)),
    deriv (a : ℂ → ℂ) w ^ 2 / (1 - conj z * (a : ℂ → ℂ) w) ^ 4 with hΘ
  set k : ℂ := 3 / π * (rho w : ℂ)⁻¹ with hk
  have hkc : conj k = k := by
    rw [hk, map_mul, map_div₀, map_inv₀, Complex.conj_ofReal, Complex.conj_ofReal, map_ofNat]
  refine ⟨fun z => k * conj (Θ z), (pk_theta_diff hΓ hw).const_mul k, ⟨‖k‖ * C, fun z hz => ?_⟩,
    fun z hz => ?_⟩
  · have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    have h1z : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
    have hT : ‖Θ z‖ ≤ ∑' a : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)),
        ‖deriv (a : ℂ → ℂ) w ^ 2 / (1 - conj z * (a : ℂ → ℂ) w) ^ 4‖ :=
      norm_tsum_le_tsum_norm (hC z hz).1
    have e : ‖((1 - ‖z‖ ^ 2 : ℝ) : ℂ) ^ 2 * (k * conj (Θ z))‖ = ‖k‖ * ((1 - ‖z‖ ^ 2) ^ 2 * ‖Θ z‖) := by
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg h1z]
      ring
    have e2 : ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) ^ 2 = (1 - (‖z‖ : ℂ) ^ 2) ^ 2 := by push_cast; ring
    rw [← e2, e]
    exact mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left hT (sq_nonneg _)).trans (hC z hz).2)
      (norm_nonneg _)
  · have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    have h1z : (1 - ‖z‖ ^ 2) ≠ 0 := by nlinarith [norm_nonneg z]
    rw [map_mul, hkc, Complex.conj_conj, hk]
    simp only [rho]
    push_cast
    have : (1 - (‖z‖ : ℂ) ^ 2) ≠ 0 := by exact_mod_cast h1z
    have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
    have h1w : (1 - ‖w‖ ^ 2) ≠ 0 := by nlinarith [norm_nonneg w]
    have : (1 - (‖w‖ : ℂ) ^ 2) ≠ 0 := by exact_mod_cast h1w
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
    ring

theorem pk_K_inv {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {w : ℂ} (hw : w ∈ unitDisc) :
    IsGammaInvD Γ fun z => 12 / π * (rho z : ℂ)⁻¹ * (rho w : ℂ)⁻¹ *
      ∑' a : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)),
        deriv (a : ℂ → ℂ) w ^ 2 / (1 - conj z * (a : ℂ → ℂ) w) ^ 4 := by
  intro δ hδ z hz
  have hsd := hΓ.1 δ hδ
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
  have hc : δ 1 0 * z + δ 1 1 ≠ 0 := fdD_denom_ne hsd hz1
  set c := δ 1 0 * z + δ 1 1 with hcdef
  have hθ := pk_theta_inv hΓ hδ hz hw
  rw [pk_deriv_mob δ hc] at hθ ⊢
  set Θ1 := ∑' a : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)),
    deriv (a : ℂ → ℂ) w ^ 2 / (1 - conj (mob δ z) * (a : ℂ → ℂ) w) ^ 4 with hΘ1
  set Θ0 := ∑' a : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)),
    deriv (a : ℂ → ℂ) w ^ 2 / (1 - conj z * (a : ℂ → ℂ) w) ^ 4 with hΘ0
  -- the hyperbolic density
  have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hid := fd_su11_identity hsd z
  have h1 : 1 - ‖mob δ z‖ ^ 2 = (1 - ‖z‖ ^ 2) / ‖c‖ ^ 2 := by
    have : mob δ z = (δ 0 0 * z + δ 0 1) / c := rfl
    rw [this, norm_div, div_pow, ← hcdef] at *
    field_simp
    linarith
  have hρ : (rho (mob δ z) : ℂ)⁻¹ = (rho z : ℂ)⁻¹ / (c * conj c) ^ 2 := by
    rw [Complex.mul_conj']
    simp only [rho, h1]
    push_cast
    have h1z : (1 - ‖z‖ ^ 2 : ℝ) ≠ 0 := by nlinarith [norm_nonneg z]
    have : (1 - (‖z‖ : ℂ) ^ 2) ≠ 0 := by exact_mod_cast h1z
    have : (‖c‖ : ℂ) ≠ 0 := by exact_mod_cast hcn.ne'
    field_simp
  show 12 / π * (rho (mob δ z) : ℂ)⁻¹ * (rho w : ℂ)⁻¹ * Θ1 * (conj ((c ^ 2)⁻¹) / (c ^ 2)⁻¹) =
    12 / π * (rho z : ℂ)⁻¹ * (rho w : ℂ)⁻¹ * Θ0
  rw [← hθ, hρ]
  have hcc : conj c ≠ 0 := (map_ne_zero _).mpr hc
  simp only [map_inv₀, map_pow]
  try rw [← hcdef]
  field_simp

theorem pk_swap {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {z w : ℂ} (hz : z ∈ unitDisc) (hw : w ∈ unitDisc) :
    (∑' a : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)),
        deriv (a : ℂ → ℂ) w ^ 2 / (1 - conj z * (a : ℂ → ℂ) w) ^ 4) =
      ∑' a : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)),
        conj (deriv (a : ℂ → ℂ) z) ^ 2 / (1 - conj ((a : ℂ → ℂ) z) * w) ^ 4 := by
  obtain ⟨e, he⟩ := fdD_inv_perm Γ
  rw [← e.tsum_eq (fun a : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)) =>
    conj (deriv (a : ℂ → ℂ) z) ^ 2 / (1 - conj ((a : ℂ → ℂ) z) * w) ^ 4)]
  refine tsum_congr fun a => ?_
  obtain ⟨g, hg, ha, hea⟩ := he a
  rw [ha, hea]
  have hsu := hΓ.1 g hg
  have hsui := isSU11_inv hsu
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
  have hp : (g⁻¹ : SL2C) 1 0 * z + (g⁻¹ : SL2C) 1 1 ≠ 0 := fdD_denom_ne hsui hz1
  obtain ⟨hcz', hback⟩ := fd_inv_step g⁻¹ hp
  rw [inv_inv] at hcz' hback
  set z' := mob g⁻¹ z with hz'
  have hz'1 : ‖z'‖ < 1 := fdD_mob_lt hsui hz1
  have hcw : g 1 0 * w + g 1 1 ≠ 0 := fdD_denom_ne hsu hw1
  have hmw : ‖mob g w‖ < 1 := fdD_mob_lt hsu hw1
  have hX : 1 - conj z * mob g w ≠ 0 := pk_one_sub_ne (by rwa [Complex.norm_conj]) hmw
  have hpq := pk_denom_inv hp hcz'
  have hcoc := pk_cocycle hsu (mem_ball_zero_iff.mpr hz'1) hw
  rw [hback] at hcoc
  rw [pk_deriv_mob g hcw, pk_deriv_mob g⁻¹ hp, ← hcoc]
  have hcz'c : conj (g 1 0 * z' + g 1 1) ≠ 0 := (map_ne_zero _).mpr hcz'
  have hpinv : (g⁻¹ : SL2C) 1 0 * z + (g⁻¹ : SL2C) 1 1 = (g 1 0 * z' + g 1 1)⁻¹ :=
    (eq_inv_of_mul_eq_one_right hpq)
  rw [hpinv]
  simp only [map_inv₀, map_pow]
  field_simp

/-- `deriv (mob g)` is continuous on `𝔻` for `g ∈ SU(1,1)`. -/
theorem pk_deriv_continuousOn {g : SL2C} (hg : IsSU11 g) : ContinuousOn (deriv (mob g)) unitDisc := by
  have h : ContinuousOn (fun z : ℂ => ((g 1 0 * z + g 1 1) ^ 2)⁻¹) unitDisc := by
    refine ContinuousOn.inv₀ (by fun_prop) fun z hz => pow_ne_zero 2 ?_
    exact fdD_denom_ne hg (mem_ball_zero_iff.mp hz)
  refine h.congr fun z hz => ?_
  exact pk_deriv_mob g (fdD_denom_ne hg (mem_ball_zero_iff.mp hz))

theorem pk_reproduce {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {β : ℂ → ℂ} (hβ : IsHarmonicD β)
    (hβΓ : IsGammaInvD Γ β) {w : ℂ} (hw : w ∈ unitDisc) :
    innerGamma Γ (fun z => 12 / π * (rho z : ℂ)⁻¹ * (rho w : ℂ)⁻¹ *
      ∑' a : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)),
        deriv (a : ℂ → ℂ) w ^ 2 / (1 - conj z * (a : ℂ → ℂ) w) ^ 4) β = conj (β w) := by
  have hF := pk_fund hΓ.1
  set F := fundDomainOn Γ unitDisc with hFdef
  have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
  set k : ℂ := 12 / π * (rho w : ℂ)⁻¹ with hk
  set h : ℂ → ℂ := fun u => k * conj (β u) / (1 - conj u * w) ^ 4 with hh
  have hβc := harmonicD_continuousOn hβ
  obtain ⟨Cβ, hCβ⟩ := harmonicD_bound hβ
  have hden : ∀ u ∈ unitDisc, 1 - conj u * w ≠ 0 := fun u hu =>
    pk_one_sub_ne (by rw [Complex.norm_conj]; exact mem_ball_zero_iff.mp hu) hw1
  have hhc : ContinuousOn h unitDisc := by
    refine ContinuousOn.div (continuousOn_const.mul (Complex.continuous_conj.comp_continuousOn hβc))
      (by fun_prop) fun u hu => pow_ne_zero 4 (hden u hu)
  -- `h` is bounded, hence integrable, on `𝔻`
  have hlow : ∀ u ∈ unitDisc, 1 - ‖w‖ ≤ ‖1 - conj u * w‖ := by
    intro u hu
    have hu1 : ‖u‖ < 1 := mem_ball_zero_iff.mp hu
    have h1 : ‖conj u * w‖ ≤ ‖w‖ := by
      rw [norm_mul, Complex.norm_conj]; nlinarith [norm_nonneg u, norm_nonneg w]
    have h2 := norm_sub_norm_le (1 : ℂ) (conj u * w)
    rw [norm_one] at h2; linarith
  have hw0 : 0 < 1 - ‖w‖ := by linarith
  have hhb : ∀ u ∈ unitDisc, ‖h u‖ ≤ ‖k‖ * Cβ / (1 - ‖w‖) ^ 4 := by
    intro u hu
    have hC0 : 0 ≤ Cβ := (norm_nonneg _).trans (hCβ u hu)
    rw [hh, norm_div, norm_mul, Complex.norm_conj, norm_pow]
    refine div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left (hCβ u hu) (norm_nonneg _))
      (by positivity) (pow_le_pow_left₀ hw0.le (hlow u hu) 4)
  have hhi : IntegrableOn h unitDisc := by
    refine Integrable.mono' (integrableOn_const (C := ‖k‖ * Cβ / (1 - ‖w‖) ^ 4)
      (by simp [unitDisc, measure_ball_lt_top.ne])) (hhc.aestronglyMeasurable measurableSet_ball) ?_
    exact (ae_restrict_iff' measurableSet_ball).mpr (Eventually.of_forall hhb)
  -- the integrand on `F`, as a series over the tiles
  set f : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)) → ℂ → ℂ := fun a z =>
    (‖deriv (a : ℂ → ℂ) z‖ ^ 2) • h ((a : ℂ → ℂ) z) with hfdef
  have hpt : ∀ z ∈ F, (12 / π * (rho z : ℂ)⁻¹ * (rho w : ℂ)⁻¹ *
      ∑' a : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)),
        deriv (a : ℂ → ℂ) w ^ 2 / (1 - conj z * (a : ℂ → ℂ) w) ^ 4) * conj (β z) * rho z =
      ∑' a, f a z := by
    intro z hzF
    have hz : z ∈ unitDisc := hF.2.1 hzF
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    have hρ : (rho z : ℂ) ≠ 0 := by
      have : 0 < rho z := by
        unfold rho; have : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
        positivity
      exact_mod_cast this.ne'
    rw [pk_swap hΓ.1 hz hw]
    have e1 : 12 / π * (rho z : ℂ)⁻¹ * (rho w : ℂ)⁻¹ *
        (∑' a : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)),
          conj (deriv (a : ℂ → ℂ) z) ^ 2 / (1 - conj ((a : ℂ → ℂ) z) * w) ^ 4) * conj (β z) * rho z =
        ∑' a : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)),
          k * (conj (deriv (a : ℂ → ℂ) z) ^ 2 / (1 - conj ((a : ℂ → ℂ) z) * w) ^ 4) * conj (β z) := by
      rw [← tsum_mul_left, ← tsum_mul_right, ← tsum_mul_right]
      refine tsum_congr fun a => ?_
      rw [hk]; field_simp
    rw [e1]
    refine tsum_congr fun a => ?_
    obtain ⟨_, g, hg, rfl⟩ := a
    have hsu := hΓ.1.1 g hg
    have hc : g 1 0 * z + g 1 1 ≠ 0 := fdD_denom_ne hsu hz1
    have hd : deriv (mob g) z ≠ 0 := by rw [pk_deriv_mob g hc]; exact inv_ne_zero (pow_ne_zero 2 hc)
    have hdc : conj (deriv (mob g) z) ≠ 0 := (map_ne_zero _).mpr hd
    have hinv := hβΓ g hg z hz
    -- `conj β(z) = conj β(gz) · g'(z) / \overline{g'(z)}`
    have hβz : conj (β z) = conj (β (mob g z)) * (deriv (mob g) z / conj (deriv (mob g) z)) := by
      rw [← hinv, map_mul, map_div₀, Complex.conj_conj]
    show k * (conj (deriv (mob g) z) ^ 2 / (1 - conj (mob g z) * w) ^ 4) * conj (β z) =
      (‖deriv (mob g) z‖ ^ 2 : ℝ) • (k * conj (β (mob g z)) / (1 - conj (mob g z) * w) ^ 4)
    rw [hβz, Complex.real_smul]
    push_cast
    rw [← Complex.mul_conj']
    have hmz : mob g z ∈ unitDisc := mem_ball_zero_iff.mpr (fdD_mob_lt hsu hz1)
    have := hden _ hmz
    field_simp
  -- measurability of the tiles' integrands on `F`
  have hfm : ∀ a, AEStronglyMeasurable (f a) (volume.restrict F) := by
    rintro ⟨_, g, hg, rfl⟩
    have hsu := hΓ.1.1 g hg
    have hcont : ContinuousOn (fun z => (‖deriv (mob g) z‖ ^ 2) • h (mob g z)) unitDisc := by
      refine ContinuousOn.smul ((pk_deriv_continuousOn hsu).norm.pow 2) ?_
      have hmob : ContinuousOn (mob g) unitDisc := fun z hz =>
        (fd_mob_differentiableAt g (fdD_denom_ne hsu (mem_ball_zero_iff.mp hz))).continuousAt.continuousWithinAt
      exact hhc.comp hmob fun z hz => mem_ball_zero_iff.mpr (fdD_mob_lt hsu (mem_ball_zero_iff.mp hz))
    exact (hcont.mono hF.2.1).aestronglyMeasurable hF.1
  -- the Tonelli bound
  have hfin : ∑' a, ∫⁻ z in F, ‖f a z‖ₑ ≠ ∞ := by
    have hu := fdD_unfold hΓ.1 hF (fun u => ‖h u‖ₑ)
    have heq : ∀ a : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)), ∫⁻ z in F, ‖f a z‖ₑ =
        ∫⁻ z in F, ENNReal.ofReal (‖deriv (a : ℂ → ℂ) z‖ ^ 2) * ‖h ((a : ℂ → ℂ) z)‖ₑ := by
      intro a
      refine lintegral_congr fun z => ?_
      rw [hfdef, enorm_smul, Real.enorm_eq_ofReal (sq_nonneg _)]
    rw [tsum_congr heq, ← hu]
    exact (hhi.hasFiniteIntegral.lt_top).ne
  haveI : DiscreteTopology Γ := hΓ.1.2
  haveI : Countable ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)) :=
    ((fd_countable (Γ := Γ)).image _).to_subtype
  unfold innerGamma quotIntD
  rw [← hFdef, setIntegral_congr_fun hF.1 hpt, integral_tsum hfm hfin,
    (fdD_hasSum_integral_unfold hΓ.1 hF hhi).tsum_eq]
  -- Bergman reproduction
  have hrep := harmonicProjD_self hβ hw
  unfold harmonicProjD at hrep
  have h1w : (1 - ‖w‖ ^ 2 : ℝ) ≠ 0 := by nlinarith [norm_nonneg w]
  have h1w' : (1 - (‖w‖ : ℂ) ^ 2) ≠ 0 := by exact_mod_cast h1w
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : (∫ u in unitDisc, h u) = k * conj (∫ ζ in unitDisc, β ζ / (1 - ζ * conj w) ^ 4) := by
    rw [← integral_conj, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_ball fun u _ => ?_
    simp only [hh, map_div₀, map_pow, map_sub, map_one, map_mul, Complex.conj_conj]
    ring
  rw [hI]
  have hJ : (∫ ζ in unitDisc, β ζ / (1 - ζ * conj w) ^ 4) = π * β w / (3 * (1 - (‖w‖ : ℂ) ^ 2) ^ 2) := by
    set I := ∫ ζ in unitDisc, β ζ / (1 - ζ * conj w) ^ 4 with hIdef
    rw [← hrep]
    push_cast
    field_simp
  rw [hJ, hk]
  simp only [map_div₀, map_mul, map_pow, map_sub, map_one, Complex.conj_ofReal, map_ofNat]
  simp only [rho]
  push_cast
  field_simp
  try ring

theorem pk_inner_sum {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {d : ℕ} (b : Fin d → ℂ → ℂ)
    (hb : ∀ n, IsHarmonicD (b n) ∧ IsGammaInvD Γ (b n)) (c : Fin d → ℂ) {f : ℂ → ℂ}
    (hf : ∀ z ∈ unitDisc, f z = ∑ n, c n * b n z) (m : Fin d) :
    innerGamma Γ f (b m) = ∑ n, c n * innerGamma Γ (b n) (b m) := by
  have hF := pk_fund hΓ.1
  have hρ : IntegrableOn (fun z => (rho z : ℂ)) (fundDomainOn Γ unitDisc) :=
    (idc_rho_integrableOn hΓ hF).ofReal
  have hint : ∀ n, IntegrableOn (fun z => b n z * conj (b m z) * rho z) (fundDomainOn Γ unitDisc) := by
    intro n
    obtain ⟨Cn, hCn⟩ := harmonicD_bound (hb n).1
    obtain ⟨Cm, hCm⟩ := harmonicD_bound (hb m).1
    have hcont : ContinuousOn (fun z => b n z * conj (b m z)) unitDisc :=
      (harmonicD_continuousOn (hb n).1).mul
        (Complex.continuous_conj.comp_continuousOn (harmonicD_continuousOn (hb m).1))
    refine Integrable.bdd_mul (c := Cn * Cm) hρ ((hcont.mono hF.2.1).aestronglyMeasurable hF.1) ?_
    refine (ae_restrict_iff' hF.1).mpr (Eventually.of_forall fun z hz => ?_)
    have hz := hF.2.1 hz
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hCn z hz) (hCm z hz) (norm_nonneg _) ((norm_nonneg _).trans (hCn z hz))
  unfold innerGamma quotIntD
  rw [setIntegral_congr_fun hF.1 (g := fun z => ∑ n, c n * (b n z * conj (b m z) * rho z))
    (fun z hz => by rw [hf z (hF.2.1 hz), Finset.sum_mul, Finset.sum_mul]; congr 1; funext n; ring)]
  rw [integral_finsetSum _ fun n _ => (hint n).const_mul (c n)]
  exact Finset.sum_congr rfl fun n _ => integral_const_mul _ _

/-! ### Assembly -/

theorem pk_projector_kernel {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {d : ℕ} (b : Fin d → ℂ → ℂ)
    (hb : ∀ n, IsHarmonicD (b n) ∧ IsGammaInvD Γ (b n))
    (hon : ∀ m n, innerGamma Γ (b m) (b n) = if m = n then 1 else 0)
    (hspan : ∀ μ, IsHarmonicD μ → IsGammaInvD Γ μ → ∃ c : Fin d → ℂ, ∀ z ∈ unitDisc, μ z = ∑ n, c n * b n z)
    {z w : ℂ} (hz : z ∈ unitDisc) (hw : w ∈ unitDisc) :
    ∑ n, b n z * conj (b n w) =
      12 / π * (rho z : ℂ)⁻¹ * (rho w : ℂ)⁻¹ *
        ∑' γ : (fun g : SL2C => mob g) '' (Γ : Set SL2C),
          deriv (γ : ℂ → ℂ) w ^ 2 / (1 - conj z * (γ : ℂ → ℂ) w) ^ 4 := by
  obtain ⟨c, hc⟩ := hspan _ (pk_K_harmonic hΓ.1 hw) (pk_K_inv hΓ.1 hw)
  have hcm : ∀ m, c m = conj (b m w) := by
    intro m
    have h1 := pk_inner_sum hΓ b hb c hc m
    rw [pk_reproduce hΓ (hb m).1 (hb m).2 hw] at h1
    simp only [hon, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h1
    exact h1.symm
  rw [hc z hz]
  exact Finset.sum_congr rfl fun n _ => by rw [hcm n, mul_comm]

/-- (TT:3444–3448) The kernel of the orthogonal projector `P : L²(𝔻, Γ) → Ω^{-1,1}(𝔻, Γ)`. For an orthonormal basis
`μ₁, …, μ_d` of `Ω^{-1,1}(𝔻, Γ)` for `( , )_Γ`:
`P(z, w) = Σ_n μ_n(z) \overline{μ_n(w)} = (12/π) ρ(z)⁻¹ ρ(w)⁻¹ Σ_{γ ∈ Γ} γ'(w)²/(1 - z̄ γ(w))⁴`
(the sum over `Γ/{±1}`; it converges absolutely). -/
theorem projector_kernel {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {d : ℕ} (b : Fin d → ℂ → ℂ)
    (hb : ∀ n, IsHarmonicD (b n) ∧ IsGammaInvD Γ (b n))
    (hon : ∀ m n, innerGamma Γ (b m) (b n) = if m = n then 1 else 0)
    (hspan : ∀ μ, IsHarmonicD μ → IsGammaInvD Γ μ → ∃ c : Fin d → ℂ, ∀ z ∈ unitDisc, μ z = ∑ n, c n * b n z)
    {z w : ℂ} (hz : z ∈ unitDisc) (hw : w ∈ unitDisc) :
    ∑ n, b n z * conj (b n w) =
      12 / π * (rho z : ℂ)⁻¹ * (rho w : ℂ)⁻¹ *
        ∑' γ : (fun g : SL2C => mob g) '' (Γ : Set SL2C),
          deriv (γ : ℂ → ℂ) w ^ 2 / (1 - conj z * (γ : ℂ → ℂ) w) ^ 4 :=
  pk_projector_kernel hΓ b hb hon hspan hz hw

end TakhtajanTeo
