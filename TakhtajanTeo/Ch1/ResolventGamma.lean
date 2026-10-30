import TakhtajanTeo.Ch1.ResolventRationalKernel

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real Matrix

noncomputable section
namespace TakhtajanTeo
open LiZhongQC
set_option autoImplicit false

theorem isSU11_mul {g h : SL2C} (hg : IsSU11 g) (hh : IsSU11 h) : IsSU11 (g * h) := by
  have e := fd_mul_entries g h
  refine ⟨?_, ?_⟩
  · rw [e, e, hg.1, hg.2, hh.1, hh.2]; simp [map_add, map_mul]; ring
  · rw [e, e, hg.1, hg.2, hh.1, hh.2]; simp [map_add, map_mul]; ring

theorem gam_mob_one (z : ℂ) : mob (1 : SL2C) z = z := by simp [mob]

theorem gam_RK1 {g : SL2C} (hg : IsSU11 g) {z w : ℂ} (hz : 1 < ‖z‖) (hw : 1 < ‖w‖) :
    resolventKernel (mob g z) (mob g w) = resolventKernel z w :=
  (RK1 z w).2 g hg (Or.inr ⟨hz, hw⟩)

/-- `D_{g m}(w) = 0` when `D_m(w) ≠ 0` and the composite has a pole. -/
theorem gam_mul_denom_zero {g m : SL2C} {w : ℂ} (hm : m 1 0 * w + m 1 1 ≠ 0)
    (hg : g 1 0 * mob m w + g 1 1 = 0) : (g * m : SL2C) 1 0 * w + (g * m : SL2C) 1 1 = 0 := by
  have e := fd_mul_entries g m
  have hmw : mob m w = (m 0 0 * w + m 0 1) / (m 1 0 * w + m 1 1) := rfl
  rw [hmw] at hg
  rw [e, e]
  have h2 : g 1 0 * ((m 0 0 * w + m 0 1) / (m 1 0 * w + m 1 1)) + g 1 1 =
      (g 1 0 * (m 0 0 * w + m 0 1) + g 1 1 * (m 1 0 * w + m 1 1)) / (m 1 0 * w + m 1 1) := by
    rw [mul_div_assoc', div_add' _ _ _ hm]
  rw [h2, div_eq_zero_iff] at hg
  rcases hg with hg | hg
  · linear_combination hg
  · exact absurd hg hm

theorem gam_K_zero {a b : ℂ} (h : ‖a‖ = ‖b‖) : resolventKernel a 0 = resolventKernel b 0 := by
  unfold resolventKernel pointPair
  simp [h]

theorem gam_norm_entries {g : SL2C} (hg : IsSU11 g) :
    ‖g 1 0‖ = ‖g 0 1‖ ∧ ‖g 1 1‖ = ‖g 0 0‖ := by
  rw [hg.1, hg.2]; simp

theorem gam_pole_norm {g : SL2C} (hg : IsSU11 g) (hg10 : g 1 0 ≠ 0) :
    1 < ‖g 0 0 / g 1 0‖ := by
  have h := fd_su11_det hg
  obtain ⟨e1, _⟩ := gam_norm_entries hg
  have hpos : 0 < ‖g 1 0‖ := norm_pos_iff.mpr hg10
  rw [norm_div, lt_div_iff₀ hpos, one_mul]
  by_contra hc
  have : ‖g 0 0‖ ≤ ‖g 1 0‖ := not_lt.mp hc
  rw [e1] at this
  nlinarith [norm_nonneg (g 0 0), norm_nonneg (g 0 1)]

/-- Invariance of the resolvent kernel under `SU(1,1)` with arbitrary (also pole) images. -/
theorem gam_master {g h : SL2C} (hg : IsSU11 g) (hh : IsSU11 h) {z w : ℂ} (hz : 1 < ‖z‖)
    (hw : 1 < ‖w‖) :
    resolventKernel (mob g z) (mob h w) = resolventKernel z (mob (g⁻¹ * h) w) := by
  set m : SL2C := g⁻¹ * h with hm
  have hmSU : IsSU11 m := isSU11_mul (isSU11_inv hg) hh
  have hgm : g * m = h := by rw [hm]; group
  by_cases hDm : m 1 0 * w + m 1 1 = 0
  · have hN : m 0 0 * w + m 0 1 ≠ 0 := fun h0 => fd_not_both_zero m w ⟨h0, hDm⟩
    have hmw : mob m w = 0 := by unfold mob; rw [hDm]; simp
    rw [hmw]
    have e := fd_mul_entries g m
    have hDh : h 1 0 * w + h 1 1 = g 1 0 * (m 0 0 * w + m 0 1) := by
      rw [← hgm, e, e]; linear_combination (g 1 1) * hDm
    have hNh : h 0 0 * w + h 0 1 = g 0 0 * (m 0 0 * w + m 0 1) := by
      rw [← hgm, e, e]; linear_combination (g 0 1) * hDm
    obtain ⟨n1, n2⟩ := gam_norm_entries hg
    by_cases hg10 : g 1 0 = 0
    · have hg01 : g 0 1 = 0 := by
        have := hg.1; rw [hg10] at this; simpa using this.symm
      have hv : mob h w = 0 := by unfold mob; rw [hDh, hg10]; simp
      rw [hv]
      have hg00 : ‖g 0 0‖ = 1 := by
        have := fd_su11_det hg
        rw [hg01] at this; simp at this
        rcases this with h | h
        · exact h
        · nlinarith [norm_nonneg (g 0 0)]
      have hnorm : ‖mob g z‖ = ‖z‖ := by
        have : mob g z = g 0 0 * z / g 1 1 := by unfold mob; rw [hg10, hg01]; simp
        rw [this, norm_div, norm_mul, n2, hg00]; simp
      exact gam_K_zero hnorm
    · have hv : mob h w = g 0 0 / g 1 0 := by
        unfold mob; rw [hDh, hNh]; field_simp
      rw [hv]
      have hv1 := gam_pole_norm hg hg10
      by_cases hDg : g 1 0 * z + g 1 1 = 0
      · have hu : mob g z = 0 := by unfold mob; rw [hDg]; simp
        rw [hu]
        have hzv : ‖z‖ = ‖g 0 0 / g 1 0‖ := by
          have : z = -g 1 1 / g 1 0 := by
            field_simp; linear_combination hDg
          rw [this, norm_div, norm_neg, n2, norm_div]
        rw [(RK1 0 (g 0 0 / g 1 0)).1]
        exact gam_K_zero hzv.symm
      · have hu1 := fd_mob_exterior hg hz hDg
        have key := gam_RK1 (isSU11_inv hg) hu1 hv1
        rw [(fd_inv_step g hDg).2] at key
        obtain ⟨e00, e01, e10, e11⟩ := fd_inv_entries g
        have : mob g⁻¹ (g 0 0 / g 1 0) = 0 := by
          unfold mob
          have : (g⁻¹ : SL2C) 1 0 * (g 0 0 / g 1 0) + (g⁻¹ : SL2C) 1 1 = 0 := by
            rw [e10, e11]; field_simp; ring
          rw [this]; simp
        rw [this] at key
        exact key.symm
  · have ht : 1 < ‖mob m w‖ := fd_mob_exterior hmSU hw hDm
    have hv : mob h w = mob g (mob m w) := by
      by_cases hDg : g 1 0 * mob m w + g 1 1 = 0
      · have h1 := gam_mul_denom_zero hDm hDg
        have h3 : mob (g * m) w = 0 := by unfold mob; rw [h1]; simp
        have h2 : mob g (mob m w) = 0 := by
          have : mob g (mob m w) = (g 0 0 * mob m w + g 0 1) / (g 1 0 * mob m w + g 1 1) := rfl
          rw [this, hDg, div_zero]
        rw [← hgm, h3, h2]
      · rw [← hgm]; exact (fd_mob_mul hDm hDg).2
    rw [hv]
    exact gam_RK1 hg hz ht

theorem gam_mul_neg (g k : SL2C) : g * -k = -(g * k) := by
  ext i j
  simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg, Matrix.mul_neg]

theorem gam_mob_mul_congr (g : SL2C) {k l : SL2C} (h : mob k = mob l) : mob (g * k) = mob (g * l) := by
  rcases fd_mob_eq h with rfl | rfl
  · rfl
  · rw [gam_mul_neg, fd_mob_neg]

/-- Left multiplication by an element of `Γ` permutes the actions. -/
theorem gam_equiv_mul (Γ : Subgroup SL2C) {g : SL2C} (hg : g ∈ Γ) :
    ∃ e : ((fun k : SL2C => mob k) '' (Γ : Set SL2C)) ≃ ((fun k : SL2C => mob k) '' (Γ : Set SL2C)),
      ∀ (a : ((fun k : SL2C => mob k) '' (Γ : Set SL2C))) (h : SL2C), h ∈ Γ → mob h = a.1 →
        (e a).1 = mob (g * h) := by
  classical
  set A := (fun k : SL2C => mob k) '' (Γ : Set SL2C) with hA
  let rep : A → SL2C := fun b => Classical.choose b.2
  have hrep : ∀ b : A, rep b ∈ Γ ∧ mob (rep b) = b.1 := fun b => Classical.choose_spec b.2
  let L : (g' : SL2C) → g' ∈ Γ → A → A := fun g' hg' a => ⟨mob (g' * rep a), g' * rep a, Γ.mul_mem hg' (hrep a).1, rfl⟩
  have hL : ∀ (g' : SL2C) (hg' : g' ∈ Γ) (a : A) (h : SL2C), h ∈ Γ → mob h = a.1 →
      (L g' hg' a).1 = mob (g' * h) := by
    intro g' hg' a h hh hha
    exact gam_mob_mul_congr g' ((hrep a).2.trans hha.symm)
  refine ⟨⟨L g hg, L g⁻¹ (Γ.inv_mem hg), ?_, ?_⟩, fun a h hh hha => hL g hg a h hh hha⟩
  · intro a
    apply Subtype.ext
    rw [hL g⁻¹ (Γ.inv_mem hg) (L g hg a) (g * rep a) (Γ.mul_mem hg (hrep a).1) rfl]
    rw [← mul_assoc, inv_mul_cancel, one_mul]; exact (hrep a).2
  · intro a
    apply Subtype.ext
    rw [hL g hg (L g⁻¹ (Γ.inv_mem hg) a) (g⁻¹ * rep a) (Γ.mul_mem (Γ.inv_mem hg) (hrep a).1) rfl]
    rw [← mul_assoc, mul_inv_cancel, one_mul]; exact (hrep a).2

/-- Inversion permutes the actions. -/
theorem gam_equiv_inv (Γ : Subgroup SL2C) :
    ∃ e : ((fun k : SL2C => mob k) '' (Γ : Set SL2C)) ≃ ((fun k : SL2C => mob k) '' (Γ : Set SL2C)),
      ∀ (a : ((fun k : SL2C => mob k) '' (Γ : Set SL2C))) (h : SL2C), h ∈ Γ → mob h = a.1 →
        (e a).1 = mob h⁻¹ := by
  classical
  set A := (fun k : SL2C => mob k) '' (Γ : Set SL2C) with hA
  let rep : A → SL2C := fun b => Classical.choose b.2
  have hrep : ∀ b : A, rep b ∈ Γ ∧ mob (rep b) = b.1 := fun b => Classical.choose_spec b.2
  let ι : A → A := fun b => ⟨mob (rep b)⁻¹, (rep b)⁻¹, Γ.inv_mem (hrep b).1, rfl⟩
  have hι : ∀ (a : A) (h : SL2C), mob h = a.1 → (ι a).1 = mob h⁻¹ := by
    intro a h hha
    show mob (rep a)⁻¹ = mob h⁻¹
    have h1 : mob (rep a) = mob h := (hrep a).2.trans hha.symm
    rcases fd_mob_eq h1 with h2 | h2
    · rw [h2]
    · rw [h2, fd_inv_neg, fd_mob_neg]
  have hinv : Function.Involutive ι := by
    intro a
    apply Subtype.ext
    have := hι (ι a) (rep a)⁻¹ rfl
    rw [this, inv_inv]; exact (hrep a).2
  refine ⟨hinv.toPerm, fun a h _ hha => hι a h hha⟩

theorem gam_clause3 {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {g : SL2C} (hg : g ∈ Γ) {z w : ℂ}
    (hz : 1 < ‖z‖) (hw : 1 < ‖w‖) :
    resolventKernelGamma Γ (mob g z) w = resolventKernelGamma Γ z w := by
  obtain ⟨e, he⟩ := gam_equiv_mul Γ (Γ.inv_mem hg)
  unfold resolventKernelGamma
  rw [← e.tsum_eq (fun b => resolventKernel z ((b : ℂ → ℂ) w))]
  refine tsum_congr fun a => ?_
  obtain ⟨h, hh, hha⟩ := a.2
  have hha' : mob h = a.1 := hha
  rw [he a h hh hha', ← hha']
  exact gam_master (hΓ.1 g hg) (hΓ.1 h hh) hz hw

theorem gam_clause2 {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {z w : ℂ}
    (hz : 1 < ‖z‖) (hw : 1 < ‖w‖) :
    resolventKernelGamma Γ z w = resolventKernelGamma Γ w z := by
  obtain ⟨e, he⟩ := gam_equiv_inv Γ
  unfold resolventKernelGamma
  rw [← e.tsum_eq (fun b => resolventKernel w ((b : ℂ → ℂ) z))]
  refine tsum_congr fun a => ?_
  obtain ⟨h, hh, hha⟩ := a.2
  have hha' : mob h = a.1 := hha
  rw [he a h hh hha', ← hha']
  have := gam_master (hΓ.1 h hh) (hΓ.1 1 Γ.one_mem) (z := w) (w := z) hw hz
  rw [gam_mob_one, mul_one] at this
  rw [(RK1 z (mob h w)).1, this]

/-! ### Positivity and Harnack inequality for the scalar kernel -/

/-- The scalar kernel is invariant under `x ↦ -1 - x` (the totalized pole). -/
theorem gam_scalar_flip (x : ℝ) :
    (2 * (-1 - x) + 1) / (2 * π) * Real.log (((-1 - x) + 1) / (-1 - x)) - 1 / π =
      (2 * x + 1) / (2 * π) * Real.log ((x + 1) / x) - 1 / π := by
  have h : ((-1 - x) + 1) / (-1 - x) = ((x + 1) / x)⁻¹ := by
    rw [inv_div]; rw [show (-1 - x + 1) = -x by ring, show (-1 - x) = -(x + 1) by ring, neg_div_neg_eq]
  rw [h, Real.log_inv]
  ring

theorem gam_K_zero_pos {z : ℂ} (hz : 1 < ‖z‖) : 0 < resolventKernel z 0 := by
  have hs : 0 < ‖z‖ ^ 2 - 1 := by nlinarith
  have hx : pointPair z 0 = -1 - 1 / (‖z‖ ^ 2 - 1) := by
    unfold pointPair
    simp only [sub_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_one]
    have h1 : ‖z‖ ^ 2 - 1 ≠ 0 := hs.ne'
    have h2 : 1 - ‖z‖ ^ 2 ≠ 0 := by intro h; apply h1; linarith
    field_simp
    ring
  unfold resolventKernel
  rw [hx, gam_scalar_flip]
  exact resolvent_scalar_pos (by positivity)

theorem gam_K_pos {z u : ℂ} (hz : 1 < ‖z‖) (hu : 1 < ‖u‖ ∨ u = 0) (hne : u ≠ z) : 0 < resolventKernel z u := by
  rcases hu with hu | rfl
  · exact RK2 hne.symm (Or.inr ⟨hz, hu⟩)
  · exact gam_K_zero_pos hz

/-- Harnack inequality for the scalar kernel. -/
theorem gam_scalar_harnack {x y l : ℝ} (hx : 0 < x) (hy : 0 < y) (hl : 1 ≤ l) (hxy : y ≤ l * x) :
    (2 * x + 1) / (2 * π) * Real.log ((x + 1) / x) - 1 / π ≤
      l ^ 2 * ((2 * y + 1) / (2 * π) * Real.log ((y + 1) / y) - 1 / π) := by
  rw [resolvent_scalar_rational_integral hx, resolvent_scalar_rational_integral hy]
  have hint : ∀ u : ℝ, 0 < u → IntervalIntegrable (fun t : ℝ => t * (1 - t) / (u + t) ^ 2) volume 0 1 := by
    intro u hu
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have ht0 : 0 ≤ t := by simpa using ht.1
    exact ((continuousAt_id.mul (continuousAt_const.sub continuousAt_id)).div
      ((continuousAt_const.add continuousAt_id).pow 2)
        (pow_ne_zero 2 (by linarith : u + t ≠ 0))).continuousWithinAt
  have hle : (∫ t in (0 : ℝ)..1, t * (1 - t) / (x + t) ^ 2) ≤
      ∫ t in (0 : ℝ)..1, l ^ 2 * (t * (1 - t) / (y + t) ^ 2) := by
    apply intervalIntegral.integral_mono_on zero_le_one (hint x hx) ((hint y hy).const_mul _)
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    have ht1 : t ≤ 1 := ht.2
    have h1 : 0 < y + t := by linarith
    have h2 : 0 < x + t := by linarith
    have hnum : 0 ≤ t * (1 - t) := mul_nonneg ht0 (by linarith)
    have hsq : (y + t) ^ 2 ≤ l ^ 2 * (x + t) ^ 2 := by
      have : y + t ≤ l * (x + t) := by nlinarith
      nlinarith [this, h1]
    calc t * (1 - t) / (x + t) ^ 2 ≤ l ^ 2 * (t * (1 - t)) / (y + t) ^ 2 := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [mul_le_mul_of_nonneg_left hsq hnum]
      _ = l ^ 2 * (t * (1 - t) / (y + t) ^ 2) := by ring
  rw [intervalIntegral.integral_const_mul] at hle
  calc 1 / (2 * π) * ∫ t in (0 : ℝ)..1, t * (1 - t) / (x + t) ^ 2
      ≤ 1 / (2 * π) * (l ^ 2 * ∫ t in (0 : ℝ)..1, t * (1 - t) / (y + t) ^ 2) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = _ := by ring

/-! ### A triangle-type inequality for the point-pair invariant -/

theorem gam_pp_eq (z w : ℂ) :
    pointPair z w = ‖z - w‖ ^ 2 / ((‖z‖ ^ 2 - 1) * (‖w‖ ^ 2 - 1)) := by
  unfold pointPair; congr 1; ring

theorem gam_ptolemy {z u v : ℂ} (hu : 1 < ‖u‖) :
    (‖u‖ ^ 2 - 1) * ‖z - v‖ ≤ ‖z - u‖ * ‖1 - conj u * v‖ + ‖v - u‖ * ‖1 - conj u * z‖ := by
  have hu2 : u * conj u = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hid : ((‖u‖ ^ 2 - 1 : ℝ) : ℂ) * (z - v) =
      (v - u) * (1 - conj u * z) - (z - u) * (1 - conj u * v) := by
    push_cast at hu2 ⊢
    linear_combination (v - z) * hu2
  have hpos : 0 ≤ ‖u‖ ^ 2 - 1 := by nlinarith
  have h := congrArg norm hid
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos] at h
  rw [h]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  linarith

theorem gam_one_sub_sq {u v : ℂ} :
    ‖1 - conj u * v‖ ^ 2 = (‖u‖ ^ 2 - 1) * (‖v‖ ^ 2 - 1) + ‖u - v‖ ^ 2 := by
  have h := normSq_blaschke_key u v
  simp only [Complex.normSq_eq_norm_sq] at h
  rw [norm_sub_rev u v]
  linarith [h]

theorem gam_pp_young {z u v : ℂ} (hz : 1 < ‖z‖) (hu : 1 < ‖u‖) (hv : 1 < ‖v‖) :
    pointPair z v ≤ 2 * pointPair z u * (1 + pointPair u v) + 2 * pointPair u v * (1 + pointPair z u) := by
  have ha : 0 < ‖z‖ ^ 2 - 1 := by nlinarith
  have hb : 0 < ‖u‖ ^ 2 - 1 := by nlinarith
  have hc : 0 < ‖v‖ ^ 2 - 1 := by nlinarith
  set a := ‖z‖ ^ 2 - 1 with hadef
  set b := ‖u‖ ^ 2 - 1 with hbdef
  set c := ‖v‖ ^ 2 - 1 with hcdef
  have hpt := gam_ptolemy (z := z) (v := v) hu
  have e1 := gam_one_sub_sq (u := u) (v := v)
  have e2 := gam_one_sub_sq (u := u) (v := z)
  rw [norm_sub_rev v u] at hpt
  have hsq : (b * ‖z - v‖) ^ 2 ≤ 2 * (‖z - u‖ ^ 2 * ‖1 - conj u * v‖ ^ 2) +
      2 * (‖u - v‖ ^ 2 * ‖1 - conj u * z‖ ^ 2) := by
    have h0 : 0 ≤ b * ‖z - v‖ := by positivity
    have := pow_le_pow_left₀ h0 hpt 2
    refine this.trans ?_
    nlinarith [sq_nonneg (‖z - u‖ * ‖1 - conj u * v‖ - ‖u - v‖ * ‖1 - conj u * z‖)]
  rw [e1] at hsq
  rw [e2, norm_sub_rev u z] at hsq
  simp only [gam_pp_eq]
  rw [← hadef, ← hbdef, ← hcdef]
  have hR : 2 * (‖z - u‖ ^ 2 / (a * b)) * (1 + ‖u - v‖ ^ 2 / (b * c)) +
      2 * (‖u - v‖ ^ 2 / (b * c)) * (1 + ‖z - u‖ ^ 2 / (a * b)) =
      (2 * ‖z - u‖ ^ 2 * (b * c + ‖u - v‖ ^ 2) + 2 * ‖u - v‖ ^ 2 * (a * b + ‖z - u‖ ^ 2)) /
        (a * b ^ 2 * c) := by
    field_simp
  rw [hR, div_le_div_iff₀ (by positivity) (by positivity)]
  have := mul_le_mul_of_nonneg_left hsq (le_of_lt (mul_pos ha hc))
  nlinarith [this]

/-! ### Finiteness of sublevel sets around a point `z` -/

theorem gam_entries_of_bounds {g : SL2C} (hg : IsSU11 g) {w : ℂ} (hw : 1 < ‖w‖) {B1 B2 : ℝ}
    (hD : ‖g 1 0 * w + g 1 1‖ ≤ B1) (hN : ‖g 0 0 * w + g 0 1‖ ≤ B2) :
    ∀ i j, ‖(g : Matrix (Fin 2) (Fin 2) ℂ) i j‖ ≤ (B1 + B2) * (‖w‖ + 1) / (‖w‖ ^ 2 - 1) := by
  have hs0 : 0 < ‖w‖ ^ 2 - 1 := by nlinarith
  have hB1n : 0 ≤ B1 := (norm_nonneg _).trans hD
  have hB2n : 0 ≤ B2 := (norm_nonneg _).trans hN
  have hww : w * conj w = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hDc : g 1 0 * w + g 1 1 = conj (g 0 1) * w + conj (g 0 0) := by rw [hg.1, hg.2]
  have ha : g 0 0 * ((‖w‖ ^ 2 - 1 : ℝ) : ℂ) = (g 0 0 * w + g 0 1) * conj w - conj (g 1 0 * w + g 1 1) := by
    rw [hDc]; simp only [map_add, map_mul, Complex.conj_conj]
    push_cast
    have := hww
    push_cast at this
    linear_combination (g 0 0) * (-this)
  have hb : g 0 1 * ((‖w‖ ^ 2 - 1 : ℝ) : ℂ) = conj (g 1 0 * w + g 1 1) * w - (g 0 0 * w + g 0 1) := by
    rw [hDc]; simp only [map_add, map_mul, Complex.conj_conj]
    push_cast
    have := hww
    push_cast at this
    linear_combination (g 0 1) * (-this)
  have hw0 : 0 ≤ ‖w‖ := norm_nonneg _
  have hBa : ‖g 0 0‖ ≤ (B1 + B2) * (‖w‖ + 1) / (‖w‖ ^ 2 - 1) := by
    rw [le_div_iff₀ hs0]
    have := congrArg norm ha
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0] at this
    have h2 : ‖(g 0 0 * w + g 0 1) * conj w - conj (g 1 0 * w + g 1 1)‖ ≤
        ‖g 0 0 * w + g 0 1‖ * ‖w‖ + ‖g 1 0 * w + g 1 1‖ := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, Complex.norm_conj, Complex.norm_conj]
    nlinarith [mul_nonneg hB1n hw0, mul_nonneg hB2n hw0, mul_le_mul_of_nonneg_right hN hw0]
  have hBb : ‖g 0 1‖ ≤ (B1 + B2) * (‖w‖ + 1) / (‖w‖ ^ 2 - 1) := by
    rw [le_div_iff₀ hs0]
    have := congrArg norm hb
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0] at this
    have h2 : ‖conj (g 1 0 * w + g 1 1) * w - (g 0 0 * w + g 0 1)‖ ≤
        ‖g 1 0 * w + g 1 1‖ * ‖w‖ + ‖g 0 0 * w + g 0 1‖ := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, Complex.norm_conj]
    nlinarith [mul_nonneg hB1n hw0, mul_nonneg hB2n hw0, mul_le_mul_of_nonneg_right hD hw0]
  intro i j
  fin_cases i <;> fin_cases j
  · exact hBa
  · exact hBb
  · simpa [hg.1] using hBb
  · simpa [hg.2] using hBa

theorem gam_sublevel_finite {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {z w : ℂ} (hz : 1 < ‖z‖)
    (hw : 1 < ‖w‖) (r : ℝ) :
    {g : SL2C | g ∈ Γ ∧ ‖(g 0 0 * w + g 0 1) - z * (g 1 0 * w + g 1 1)‖ ≤ r}.Finite := by
  haveI : DiscreteTopology Γ := hΓ.2
  set s : ℝ := ‖w‖ ^ 2 - 1 with hsdef
  have hs : 0 < s := by nlinarith
  set p : ℝ := ‖z‖ with hpdef
  have hp1 : 1 < p := hz
  have hp2 : 0 < p ^ 2 - 1 := by nlinarith
  set B1 : ℝ := 1 + |r| + (2 * p * |r| + s) / (p ^ 2 - 1) with hB1
  set B2 : ℝ := B1 + √s with hB2
  refine (fd_bounded_finite (Γ := Γ) ((B1 + B2) * (‖w‖ + 1) / (‖w‖ ^ 2 - 1))).subset (fun g hg => ?_)
  refine ⟨hg.1, ?_⟩
  have hsu := hΓ.1 g hg.1
  have hid := fd_su11_identity hsu w
  set D : ℂ := g 1 0 * w + g 1 1 with hDdef
  set N : ℂ := g 0 0 * w + g 0 1 with hNdef
  have hr : ‖N - z * D‖ ≤ r := hg.2
  have hr0 : 0 ≤ r := (norm_nonneg _).trans hr
  have hrr : |r| = r := abs_of_nonneg hr0
  have hNsq : ‖N‖ ^ 2 = ‖D‖ ^ 2 + s := by rw [hid]
  have hlow : p * ‖D‖ ≤ ‖N‖ + r := by
    have h1 : ‖z * D‖ ≤ ‖N‖ + ‖N - z * D‖ := by
      have := norm_sub_le N (N - z * D)
      rw [sub_sub_cancel] at this
      linarith [norm_sub_rev N (z * D)]
    rw [norm_mul] at h1
    linarith
  have hd : ‖D‖ ≤ B1 := by
    by_cases hd1 : ‖D‖ ≤ 1
    · rw [hB1, hrr]
      have : 0 ≤ (2 * p * r + s) / (p ^ 2 - 1) := by positivity
      linarith [abs_nonneg r]
    · push_neg at hd1
      by_cases hpd : p * ‖D‖ ≤ r
      · rw [hB1, hrr]
        have : 0 ≤ (2 * p * r + s) / (p ^ 2 - 1) := by positivity
        nlinarith [norm_nonneg D]
      · push_neg at hpd
        have hsq : (p * ‖D‖ - r) ^ 2 ≤ ‖N‖ ^ 2 := by
          apply pow_le_pow_left₀ (by linarith) (by linarith)
        rw [hNsq] at hsq
        have h3 : (p ^ 2 - 1) * ‖D‖ ≤ 2 * p * r + s := by
          have h4 : (p ^ 2 - 1) * ‖D‖ ^ 2 ≤ (2 * p * r + s) * ‖D‖ := by
            nlinarith [sq_nonneg r, mul_pos (by linarith : (0 : ℝ) < ‖D‖) hs]
          nlinarith [norm_nonneg D]
        rw [hB1, hrr]
        have h5 : ‖D‖ ≤ (2 * p * r + s) / (p ^ 2 - 1) := by
          rw [le_div_iff₀ hp2]; linarith
        linarith [abs_nonneg r]
  have hN : ‖N‖ ≤ B2 := by
    rw [hB2]
    have : ‖N‖ ^ 2 ≤ (B1 + √s) ^ 2 := by
      rw [hNsq]
      nlinarith [Real.sq_sqrt hs.le, Real.sqrt_nonneg s, norm_nonneg D, mul_nonneg (norm_nonneg D) (Real.sqrt_nonneg s)]
    have hB1nonneg : 0 ≤ B1 := (norm_nonneg D).trans hd
    nlinarith [norm_nonneg N, Real.sqrt_nonneg s]
  exact gam_entries_of_bounds hsu hw hd hN

/-- A displacement smaller than both one and the source separation gives a
uniform comparison of point-pair invariants. -/
theorem gam_pp_local_comparison {z u v : ℂ}
    (hz : 1 < ‖z‖) (hu : 1 < ‖u‖) (hv : 1 < ‖v‖)
    (hsmall : pointPair u v ≤ 1) (hsep : pointPair u v ≤ pointPair z u) :
    pointPair z v ≤ 8 * pointPair z u := by
  have ha : 0 ≤ pointPair z u := by
    rw [gam_pp_eq]
    exact div_nonneg (sq_nonneg _) (mul_nonneg (by nlinarith) (by nlinarith))
  have hab := mul_le_mul_of_nonneg_left hsmall ha
  have h := gam_pp_young hz hu hv
  nlinarith

/-- The local kernel comparison needed to promote almost-everywhere convergence
of the automorphic series to convergence at each point off the orbit. -/
theorem gam_kernel_local_comparison {z u v : ℂ}
    (hz : 1 < ‖z‖) (hu : 1 < ‖u‖) (hv : 1 < ‖v‖)
    (hzu : z ≠ u) (hzv : z ≠ v)
    (hsmall : pointPair u v ≤ 1) (hsep : pointPair u v ≤ pointPair z u) :
    resolventKernel z u ≤ 64 * resolventKernel z v := by
  have h := gam_scalar_harnack
    (pointPair_pos hzu (Or.inr ⟨hz, hu⟩))
    (pointPair_pos hzv (Or.inr ⟨hz, hv⟩)) (l := 8) (by norm_num)
    (gam_pp_local_comparison hz hu hv hsmall hsep)
  norm_num only [show (8 : ℝ) ^ 2 = 64 by norm_num] at h
  exact h

end TakhtajanTeo
