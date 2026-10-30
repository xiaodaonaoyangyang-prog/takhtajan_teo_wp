import TakhtajanTeo.Ch1.S1_4_Resolvent
import TakhtajanTeo.Ch1.CauchyDifferentiableAE
import References.GardinerLakic2000.Ch03.S04_ClosedSets
import TakhtajanTeo.Ch1.QCVariationPlane
import TakhtajanTeo.Ch1.QCVariationLocalKernel

/-!
# Chapter 1, §1.5 — Variational formulas (TT:1152–1344)

* tensors of type `(l, m)` for `Γ`, pull-backs `(w_{εμ})^*(ω^ε)`, Lie derivatives `L_μ`, `L_{μ̄}`
* the upper half-plane model: `w_{εμ}` fixing `0, 1, ∞`, the kernel `R`, (1.21), `F[μ]`, `Φ[μ]` (1.22), `Φ[μ]_{zzz}`,
  the projection (1.23), Lemma 1.12, Lemma 1.13 (Ahlfors), Remark 1.14, Corollary 1.15
* the kernels `K_μ` and their variations (1.24)–(1.25)
* the unit disk model: (1.26)

**Modelling.**
- In the half-plane model a Beltrami differential on `𝕌` is a function `μ : ℂ → ℂ` read on `𝕌`.
- `w_{εμ}` is the normalized solution (`LiZhongQC.normalizedSolution`, fixing `0, 1, ∞`) for the reflection
  extension `μ(z̄)‾` to the lower half-plane.
- The `ε`-derivatives `∂/∂ε`, `∂/∂ε̄` are the Wirtinger derivatives `LiZhongQC.dz`, `LiZhongQC.dzbar` in `ε`.
- Integrals "in the principal value sense" are limits over the complement of small disks around the singular points.
- The real vector fields `∂/∂t_μ` (TT:1186–1193) are notation and are not stated. Neither is the sentence that
  "formulas similar to (1.22) hold" for the disk model (TT:1322–1328), which the memoir does not make precise; (1.26)
  is its precise instance.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

/-! ## Tensors and Lie derivatives -/

/-- A tensor of type `(l, m)` for `Γ` (model `𝔻`) (TT:1154–1157): `ω(γz) γ'(z)^l \overline{γ'(z)}^m = ω(z)` on `𝔻`
for all `γ ∈ Γ`. (The memoir also requires `ω` to be `C^∞`.) -/
def IsTensor (Γ : Subgroup SL2C) (l m : ℤ) (ω : ℂ → ℂ) : Prop :=
  ContDiffOn ℝ (⊤ : ℕ∞) ω unitDisc ∧
    ∀ g ∈ Γ, ∀ z ∈ unitDisc, ω (mob g z) * deriv (mob g) z ^ l * conj (deriv (mob g) z) ^ m = ω z

/-- The pull-back `w^*(ω) = ω ∘ w · (w_z)^l ((\bar w)_{z̄})^m` of a tensor of type `(l, m)` by a q.c. map `w`
(TT:1163). The OCR prints `(\bar w)_z`. The metric formula (6.1) `w^*(ρ) = ρ ∘ w |w_z|²` (TT:2563) requires
`(\bar w)_{z̄} = \overline{w_z}`, which is the usual convention, so that reading is used. -/
def pullbackTensor (w : ℂ → ℂ) (l m : ℤ) (ω : ℂ → ℂ) (z : ℂ) : ℂ :=
  ω (w z) * dz w z ^ l * dzbar (fun y => conj (w y)) z ^ m

/-- The Lie derivatives `L_μ ω = ∂/∂ε|_{ε=0} (w_{εμ})^*(ω^ε)` and `L_{μ̄} ω = ∂/∂ε̄|_{ε=0} (w_{εμ})^*(ω^ε)` of a
family `ω^ε` of tensors of type `(l, m)` along a family `w_ε` of q.c. maps (TT:1169). For a function on `T(Γ)`
(type `(0, 0)`) these are the directional derivatives `∂ω(μ)`, `∂̄ω(μ̄)` (TT:1181). -/
def lieDeriv (w : ℂ → ℂ → ℂ) (l m : ℤ) (ω : ℂ → ℂ → ℂ) (z : ℂ) : ℂ :=
  dz (fun ε => pullbackTensor (w ε) l m (ω ε) z) 0

/-- The anti-holomorphic Lie derivative `L_{μ̄}` (TT:1169). -/
def lieDerivBar (w : ℂ → ℂ → ℂ) (l m : ℤ) (ω : ℂ → ℂ → ℂ) (z : ℂ) : ℂ :=
  dzbar (fun ε => pullbackTensor (w ε) l m (ω ε) z) 0

/-! ## The upper half-plane model -/

/-- The reflection extension of a Beltrami differential on `𝕌` to the plane: `μ` on `𝕌`, `\overline{μ(z̄)}` on the
lower half-plane, `0` on `ℝ`. -/
def extU (μ : ℂ → ℂ) (z : ℂ) : ℂ :=
  if 0 < z.im then μ z else if z.im < 0 then conj (μ (conj z)) else 0

/-- `w_μ` in the model `𝕌` (TT:1206): the q.c. map of `ℂ` with Beltrami differential `extU μ`, fixing `0, 1, ∞`. -/
def wU (μ : ℂ → ℂ) : ℂ → ℂ := normalizedSolution (extU μ)

/-- The kernel `R(z, u) = z(z - 1)/((u - z) u (u - 1))` for the model `𝕌` (TT:1209). -/
def kernelRU (z u : ℂ) : ℂ := z * (z - 1) / ((u - z) * u * (u - 1))

/-- (TT:1209) `R(z, u) = 1/(u - z) + (z - 1)/u - z/(u - 1)`. -/
theorem kernelRU_partial_fractions {z u : ℂ} (h1 : u ≠ z) (h2 : u ≠ 0) (h3 : u ≠ 1) :
    kernelRU z u = 1 / (u - z) + (z - 1) / u - z / (u - 1) := by
  unfold kernelRU
  field_simp [sub_ne_zero.mpr h1, h2, sub_ne_zero.mpr h3]
  <;> ring

/-- **(1.21)** (TT:1199–1203). For `μ ∈ L∞(𝕌)` with `‖μ‖∞ ≤ k` and `ε` with `|ε| k < 1`:
`∂/∂ε w_{εμ}(z) = -(1/π) ∬_𝕌 R(w_{εμ}(z), w_{εμ}(u)) μ(u) (w_{εμ})_u(u)² d²u`,
`∂/∂ε̄ w_{εμ}(z) = -(1/π) ∬_𝕌 R(w_{εμ}(z), \overline{w_{εμ}(u)}) \overline{μ(u) (w_{εμ})_u(u)²} d²u`. -/
theorem eq_1_21 {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμ : IsBeltramiCoeff μ upperHalf k) {ε : ℂ} (hε : ‖ε‖ * k < 1)
    (z : ℂ) :
    dz (fun e => wU (fun u => e * μ u) z) ε =
        -(1 / π) * ∫ u in upperHalf, kernelRU (wU (fun v => ε * μ v) z) (wU (fun v => ε * μ v) u) * μ u *
          dz (wU fun v => ε * μ v) u ^ 2 ∧
      dzbar (fun e => wU (fun u => e * μ u) z) ε =
        -(1 / π) * ∫ u in upperHalf, kernelRU (wU (fun v => ε * μ v) z) (conj (wU (fun v => ε * μ v) u)) *
          conj (μ u * dz (wU fun v => ε * μ v) u ^ 2) :=
  QCV.qcv_plane_reflection_dz hk hμ hε z

/-- `F[μ] = ∂/∂ε|_{ε=0} w_{εμ}` (TT:1215). -/
def varF (μ : ℂ → ℂ) (z : ℂ) : ℂ := dz (fun e => wU (fun u => e * μ u) z) 0

/-- `Φ[μ] = ∂/∂ε̄|_{ε=0} w_{εμ}` (TT:1215). -/
def varPhi (μ : ℂ → ℂ) (z : ℂ) : ℂ := dzbar (fun e => wU (fun u => e * μ u) z) 0

/-- (1.22) for every bound `k ≥ 0` (the hypothesis `k < 1` of `eq_1_22` is not used: the formula is at `ε = 0`). -/
theorem eq_1_22_of_bounded {μ : ℂ → ℂ} {k : ℝ} (hk0 : 0 ≤ k) (hμ : IsBeltramiCoeff μ upperHalf k) (z : ℂ) :
    varF μ z = -(1 / π) * ∫ u in upperHalf, kernelRU z u * μ u ∧
      varPhi μ z = -(1 / π) * ∫ u in upperHalf, kernelRU z (conj u) * conj (μ u) := by
  have hext : extU (fun v => (0 : ℂ) * μ v) = 0 := by
    funext u
    simp only [extU, zero_mul, map_zero, ite_self, Pi.zero_apply]
  have hw0 : wU (fun v => (0 : ℂ) * μ v) = id := by
    unfold wU
    rw [hext]
    exact bB_l_normalizedSolution_zero
  have hdz : ∀ u, dz (id : ℂ → ℂ) u = 1 := by
    intro u
    simp [dz]
  obtain ⟨h1, h2⟩ := eq_1_21 (ε := 0) hk0 hμ (by simp) z
  rw [hw0] at h1 h2
  refine ⟨?_, ?_⟩
  · unfold varF
    rw [h1]
    simp only [id_eq, hdz, one_pow, mul_one]
  · unfold varPhi
    rw [h2]
    simp only [id_eq, hdz, one_pow, mul_one]

/-- **(1.22)** (TT:1221–1226). `F[μ](z) = -(1/π) ∬_𝕌 R(z, u) μ(u) d²u` and
`Φ[μ](z) = -(1/π) ∬_𝕌 R(z, ū) \overline{μ(u)} d²u`. -/
theorem eq_1_22 {μ : ℂ → ℂ} {k : ℝ} (hk0 : 0 ≤ k) (hk : k < 1) (hμ : IsBeltramiCoeff μ upperHalf k) (z : ℂ) :
    varF μ z = -(1 / π) * ∫ u in upperHalf, kernelRU z u * μ u ∧
      varPhi μ z = -(1 / π) * ∫ u in upperHalf, kernelRU z (conj u) * conj (μ u) := by
  exact eq_1_22_of_bounded hk0 hμ z

/-! ### Holomorphy of the kernel integral `z ↦ ∫_𝕌 R(z, ū) \overline{μ(u)}` (helpers for `varPhi_holomorphic`) -/

theorem measurableSet_upperHalf_aux : MeasurableSet upperHalf :=
  measurableSet_lt measurable_const Complex.measurable_im

/-- The function `‖u‖⁻¹` is locally integrable at `0` in the plane. -/
theorem phiKernel_inv_norm_integrableOn : IntegrableOn (fun u : ℂ => ‖u‖⁻¹) (ball 0 (1 / 2)) := by
  have hfin : (Module.finrank ℝ ℂ : ℝ) = 2 := by simp
  refine integrableOn_ball_of_norm_le_rpow (μ := volume) (C := 1) (α := 1) (by simp) (by rw [hfin]; norm_num) ?_ ?_
  · refine (ae_restrict_iff' measurableSet_ball).mpr (ae_of_all _ fun x _ => ?_)
    rw [Real.rpow_neg_one, norm_inv, norm_norm, one_mul]
  · exact (measurable_norm.inv).aestronglyMeasurable

/-- Integrable majorant `‖u‖⁻¹ ‖u - 1‖⁻¹ (1 + ‖u‖)⁻¹` for the kernel `R(z, ū)`. -/
theorem phiKernel_majorant_integrable :
    Integrable (fun u : ℂ => ‖u‖⁻¹ * ‖u - 1‖⁻¹ * (1 + ‖u‖)⁻¹) := by
  have hmeas : Measurable (fun u : ℂ => ‖u‖⁻¹ * ‖u - 1‖⁻¹ * (1 + ‖u‖)⁻¹) := by fun_prop
  have hA : Integrable (fun u : ℂ => (ball (0 : ℂ) (1 / 2)).indicator (fun u : ℂ => 2 * ‖u‖⁻¹) u) := by
    rw [integrable_indicator_iff measurableSet_ball]
    exact phiKernel_inv_norm_integrableOn.const_mul 2
  have hB : Integrable (fun u : ℂ => (ball (1 : ℂ) (1 / 2)).indicator (fun u : ℂ => 2 * ‖u - 1‖⁻¹) u) := by
    have := hA.comp_sub_right (1 : ℂ)
    refine this.congr (ae_of_all _ fun u => ?_)
    simp only [indicator, mem_ball, dist_eq_norm, sub_zero]
  have hC : Integrable (fun u : ℂ => 24 * (1 + ‖u‖) ^ (-(3 : ℝ))) := by
    have hfin : (Module.finrank ℝ ℂ : ℝ) < 3 := by simp; norm_num
    exact (integrable_one_add_norm (μ := volume) hfin).const_mul 24
  refine ((hA.add hB).add hC).mono' hmeas.aestronglyMeasurable (ae_of_all _ fun u => ?_)
  have hω : 0 ≤ ‖u‖⁻¹ * ‖u - 1‖⁻¹ * (1 + ‖u‖)⁻¹ := by positivity
  rw [Real.norm_of_nonneg hω]
  by_cases h0 : u ∈ ball (0 : ℂ) (1 / 2)
  · have hs : 1 / 2 ≤ ‖u - 1‖ := by
      have := norm_sub_norm_le (1 : ℂ) u
      rw [← norm_neg (u - 1), neg_sub] at *
      have h1 : ‖u‖ < 1 / 2 := by simpa using h0
      simp at this; linarith
    have h1 : ‖u - 1‖⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    have h2 : (1 + ‖u‖)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [norm_nonneg u])
    have hB0 : 0 ≤ (ball (1 : ℂ) (1 / 2)).indicator (fun u : ℂ => 2 * ‖u - 1‖⁻¹) u := by
      exact indicator_nonneg (fun _ _ => by positivity) _
    have hC0 : 0 ≤ 24 * (1 + ‖u‖) ^ (-(3 : ℝ)) := by positivity
    simp only [Pi.add_apply, indicator_of_mem h0]
    have : ‖u‖⁻¹ * ‖u - 1‖⁻¹ * (1 + ‖u‖)⁻¹ ≤ ‖u‖⁻¹ * 2 * 1 := by
      gcongr
    linarith
  · by_cases h1 : u ∈ ball (1 : ℂ) (1 / 2)
    · have hs : 1 / 2 ≤ ‖u‖ := by
        have h1' : ‖u - 1‖ < 1 / 2 := by simpa [dist_eq_norm] using h1
        have := norm_sub_norm_le (1 : ℂ) (1 - u)
        have h3 := norm_sub_norm_le (1 : ℂ) (1 - u)
        have h4 : ‖1 - u‖ = ‖u - 1‖ := norm_sub_rev 1 u
        have h5 : ‖(1 : ℂ) - (1 - u)‖ = ‖u‖ := by simp
        linarith [norm_nonneg (u - 1), norm_sub_norm_le (1 : ℂ) (1 - u), norm_one (α := ℂ)]
      have h2 : ‖u‖⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
      have h3 : (1 + ‖u‖)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [norm_nonneg u])
      have hA0 : 0 ≤ (ball (0 : ℂ) (1 / 2)).indicator (fun u : ℂ => 2 * ‖u‖⁻¹) u := by
        exact indicator_nonneg (fun _ _ => by positivity) _
      have hC0 : 0 ≤ 24 * (1 + ‖u‖) ^ (-(3 : ℝ)) := by positivity
      simp only [Pi.add_apply, indicator_of_mem h1]
      have : ‖u‖⁻¹ * ‖u - 1‖⁻¹ * (1 + ‖u‖)⁻¹ ≤ 2 * ‖u - 1‖⁻¹ * 1 := by
        gcongr
      linarith
    · have ht : 1 / 2 ≤ ‖u‖ := by simpa [dist_eq_norm] using h0
      have hs : 1 / 2 ≤ ‖u - 1‖ := by simpa [dist_eq_norm] using h1
      have hsu : ‖u‖ - 1 ≤ ‖u - 1‖ := by
        have := norm_sub_norm_le u 1
        simpa using this
      have hA0 : 0 ≤ (ball (0 : ℂ) (1 / 2)).indicator (fun u : ℂ => 2 * ‖u‖⁻¹) u := by
        exact indicator_nonneg (fun _ _ => by positivity) _
      have hB0 : 0 ≤ (ball (1 : ℂ) (1 / 2)).indicator (fun u : ℂ => 2 * ‖u - 1‖⁻¹) u := by
        exact indicator_nonneg (fun _ _ => by positivity) _
      have key : (1 + ‖u‖) ^ 3 ≤ 24 * (‖u‖ * ‖u - 1‖ * (1 + ‖u‖)) := by
        have h8 : (1 + ‖u‖) ≤ 8 * ‖u - 1‖ := by
          by_cases h3 : ‖u‖ ≤ 3
          · linarith
          · linarith
        have h3 : (1 + ‖u‖) ≤ 3 * ‖u‖ := by linarith
        have hp : 0 ≤ 1 + ‖u‖ := by positivity
        calc (1 + ‖u‖) ^ 3 = (1 + ‖u‖) * (1 + ‖u‖) * (1 + ‖u‖) := by ring
          _ ≤ (3 * ‖u‖) * (8 * ‖u - 1‖) * (1 + ‖u‖) := by gcongr
          _ = _ := by ring
      have hX : 0 < ‖u‖ * ‖u - 1‖ * (1 + ‖u‖) := by
        have : 0 < ‖u‖ := by linarith
        have : 0 < ‖u - 1‖ := by linarith
        positivity
      have hY : 0 < (1 + ‖u‖) ^ 3 := by positivity
      have : ‖u‖⁻¹ * ‖u - 1‖⁻¹ * (1 + ‖u‖)⁻¹ ≤ 24 * (1 + ‖u‖) ^ (-(3 : ℝ)) := by
        rw [show (-(3 : ℝ)) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by positivity), Real.rpow_natCast,
          ← mul_inv, ← mul_inv, ← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hX hY]
        linarith
      simp only [Pi.add_apply]
      linarith

/-- Uniform lower bound `‖ū - z‖ ≥ c (1 + ‖u‖)` for `u` in the upper half-plane and `z` near `z₀ ∈ 𝕌`. -/
theorem phiKernel_lower_bound {z₀ : ℂ} (hz₀ : z₀ ∈ upperHalf) :
    ∃ δ > 0, ∃ c, 0 < c ∧ c ≤ 1 ∧ δ ≤ z₀.im / 2 ∧
      ∀ z ∈ ball z₀ δ, ∀ u ∈ upperHalf, c * (1 + ‖u‖) ≤ ‖conj u - z‖ := by
  have hy : 0 < z₀.im := hz₀
  set δ : ℝ := z₀.im / 2 with hδ
  set R : ℝ := ‖z₀‖ + δ with hR
  have hR0 : 0 ≤ R := by positivity
  refine ⟨δ, by positivity, min (1 / 4) (z₀.im / (2 * (2 * R + 3))), by positivity, (min_le_left _ _).trans (by norm_num), le_rfl, ?_⟩
  intro z hz u hu
  have hu' : 0 < u.im := hu
  have hzz : ‖z - z₀‖ < δ := by simpa [dist_eq_norm] using hz
  have hzim : z₀.im / 2 < z.im := by
    have := abs_im_le_norm (z - z₀)
    have h2 : |z.im - z₀.im| < δ := by simpa using lt_of_le_of_lt this hzz
    have := (abs_lt.mp h2).1
    linarith
  have hznorm : ‖z‖ ≤ R := by
    have := norm_le_insert' z z₀
    linarith
  have hb1 : z₀.im / 2 ≤ ‖conj u - z‖ := by
    have := abs_im_le_norm (conj u - z)
    have h3 : (conj u - z).im = -u.im - z.im := by simp
    rw [h3] at this
    have : u.im + z.im ≤ |(-u.im - z.im)| := by
      rw [show -u.im - z.im = -(u.im + z.im) by ring, abs_neg, abs_of_pos (by linarith)]
    linarith
  have hb2 : ‖u‖ - R ≤ ‖conj u - z‖ := by
    have h4 := norm_sub_norm_le (conj u) z
    have h5 : ‖conj u‖ = ‖u‖ := by simp
    linarith
  have hc1 : min (1 / 4) (z₀.im / (2 * (2 * R + 3))) ≤ 1 / 4 := min_le_left _ _
  have hc2 : min (1 / 4) (z₀.im / (2 * (2 * R + 3))) ≤ z₀.im / (2 * (2 * R + 3)) := min_le_right _ _
  set c := min (1 / 4) (z₀.im / (2 * (2 * R + 3))) with hc
  have hc0 : 0 < c := by positivity
  by_cases hbig : 2 * R + 2 ≤ ‖u‖
  · have : (1 + ‖u‖) / 4 ≤ ‖u‖ - R := by linarith
    nlinarith [norm_nonneg u, mul_le_mul_of_nonneg_right hc1 (by positivity : (0:ℝ) ≤ 1 + ‖u‖)]
  · replace hbig := not_le.mp hbig
    have hpos : 0 < 2 * (2 * R + 3) := by positivity
    have : c * (2 * (2 * R + 3)) ≤ z₀.im := by
      have := mul_le_mul_of_nonneg_right hc2 hpos.le
      rwa [div_mul_cancel₀ _ hpos.ne'] at this
    have : c * (1 + ‖u‖) ≤ c * (2 * R + 3) := by
      apply mul_le_mul_of_nonneg_left (by linarith) hc0.le
    nlinarith

/-- Differentiation under the integral for `z ↦ ∫_𝕌 w(u) (ū - z)⁻ⁿ`, `w = m/(ū(ū-1))` (`n ≥ 1`). -/
theorem phiKernel_hasDerivAt {m : ℂ → ℂ} {k : ℝ} (hm : AEStronglyMeasurable m (volume.restrict upperHalf))
    (hb : ∀ᵐ u ∂(volume.restrict upperHalf), ‖m u‖ ≤ k) (n : ℕ) (hn : 1 ≤ n) {z₀ : ℂ} (hz₀ : z₀ ∈ upperHalf) :
    Integrable (fun u => m u / (conj u * (conj u - 1)) / (conj u - z₀) ^ (n + 1)) (volume.restrict upperHalf) ∧
      HasDerivAt (fun z => ∫ u in upperHalf, m u / (conj u * (conj u - 1)) / (conj u - z) ^ n)
        ((n : ℂ) * ∫ u in upperHalf, m u / (conj u * (conj u - 1)) / (conj u - z₀) ^ (n + 1)) z₀ := by
  obtain ⟨δ, hδ, c, hc0, hc1, hδy, hlow⟩ := phiKernel_lower_bound hz₀
  have hmeasF (j : ℕ) (z : ℂ) : AEStronglyMeasurable (fun u => m u / (conj u * (conj u - 1)) / (conj u - z) ^ j)
      (volume.restrict upperHalf) := by
    refine ((hm.aemeasurable.div (by fun_prop)).div (by fun_prop)).aestronglyMeasurable
  have hne (z : ℂ) (hz : z ∈ ball z₀ δ) (u : ℂ) (hu : u ∈ upperHalf) : conj u - z ≠ 0 := by
    intro h
    have := hlow z hz u hu
    rw [h, norm_zero] at this
    have : 0 < c * (1 + ‖u‖) := by positivity
    linarith
  set bound : ℂ → ℝ := fun u => ((n : ℝ) * |k| / c ^ (n + 1)) * (‖u‖⁻¹ * ‖u - 1‖⁻¹ * (1 + ‖u‖)⁻¹) with hbound
  have hbint : Integrable bound (volume.restrict upperHalf) :=
    (phiKernel_majorant_integrable.const_mul _).integrableOn
  -- the pointwise bound for `w / (ū - z)^(j+1)` with a constant `a`
  have hpt (j : ℕ) (z : ℂ) (hz : z ∈ ball z₀ δ) (u : ℂ) (hu : u ∈ upperHalf) (hmu : ‖m u‖ ≤ k) :
      ‖m u / (conj u * (conj u - 1)) / (conj u - z) ^ (j + 1)‖ ≤
        (|k| / c ^ (j + 1)) * (‖u‖⁻¹ * ‖u - 1‖⁻¹ * (1 + ‖u‖)⁻¹) := by
    have hu0 : 0 < ‖u‖ := norm_pos_iff.mpr (fun h => by simp [h] at hu; exact absurd hu (by simp [upperHalf]))
    have hu1 : 0 < ‖u - 1‖ := norm_pos_iff.mpr (fun h => by
      have : u = 1 := sub_eq_zero.mp h
      subst this; exact absurd hu (by simp [upperHalf]))
    have hd := hlow z hz u hu
    have hdpos : 0 < c * (1 + ‖u‖) := by positivity
    have hn1 : ‖conj u‖ = ‖u‖ := by simp
    have hn2 : ‖conj u - 1‖ = ‖u - 1‖ := by
      rw [show conj u - 1 = conj (u - 1) by simp]; exact RCLike.norm_conj _
    rw [norm_div, norm_div, norm_mul, norm_pow, hn1, hn2]
    have hpow : c ^ (j + 1) * (1 + ‖u‖) ≤ ‖conj u - z‖ ^ (j + 1) := by
      calc c ^ (j + 1) * (1 + ‖u‖) ≤ c ^ (j + 1) * (1 + ‖u‖) ^ (j + 1) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact le_self_pow₀ (by linarith [norm_nonneg u]) (by omega)
        _ = (c * (1 + ‖u‖)) ^ (j + 1) := by rw [mul_pow]
        _ ≤ ‖conj u - z‖ ^ (j + 1) := pow_le_pow_left₀ hdpos.le hd _
    have hcp : 0 < c ^ (j + 1) * (1 + ‖u‖) := by positivity
    have hkk : ‖m u‖ ≤ |k| := hmu.trans (le_abs_self k)
    calc ‖m u‖ / (‖u‖ * ‖u - 1‖) / ‖conj u - z‖ ^ (j + 1)
        ≤ |k| / (‖u‖ * ‖u - 1‖) / (c ^ (j + 1) * (1 + ‖u‖)) := by
          apply div_le_div₀ (by positivity) _ hcp hpow
          exact div_le_div_of_nonneg_right hkk (by positivity)
      _ = _ := by
          field_simp
  have hF'meas : AEStronglyMeasurable (fun u => (n : ℂ) * (m u / (conj u * (conj u - 1)) / (conj u - z₀) ^ (n + 1)))
      (volume.restrict upperHalf) := (hmeasF (n + 1) z₀).const_mul _
  have hint : Integrable (fun u => m u / (conj u * (conj u - 1)) / (conj u - z₀) ^ n) (volume.restrict upperHalf) := by
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    refine Integrable.mono' ((phiKernel_majorant_integrable.const_mul (|k| / c ^ (j + 1))).integrableOn)
      (hmeasF _ z₀) ?_
    filter_upwards [hb, ae_restrict_mem measurableSet_upperHalf_aux] with u hmu hu
    exact hpt j z₀ (mem_ball_self hδ) u hu hmu
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict upperHalf)
    (F := fun z u => m u / (conj u * (conj u - 1)) / (conj u - z) ^ n)
    (F' := fun z u => (n : ℂ) * (m u / (conj u * (conj u - 1)) / (conj u - z) ^ (n + 1)))
    (x₀ := z₀) (bound := bound) (s := ball z₀ δ) (ball_mem_nhds z₀ hδ) (Eventually.of_forall fun z => hmeasF n z) hint hF'meas ?_ hbint ?_
  · obtain ⟨h1, h2⟩ := key
    refine ⟨?_, ?_⟩
    · have := h1.const_mul ((n : ℂ)⁻¹)
      refine this.congr (ae_of_all _ fun u => ?_)
      have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
      simp only
      rw [inv_mul_cancel_left₀ hn0]
    · rw [← integral_const_mul]; exact h2
  · filter_upwards [hb, ae_restrict_mem measurableSet_upperHalf_aux] with u hmu hu
    intro z hz
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    rw [norm_mul]
    have := hpt (j + 1) z hz u hu hmu
    simp only [hbound]
    have hnn : ‖((j + 1 : ℕ) : ℂ)‖ = ((j + 1 : ℕ) : ℝ) := Complex.norm_natCast _
    rw [hnn]
    calc ((j + 1 : ℕ) : ℝ) * ‖m u / (conj u * (conj u - 1)) / (conj u - z) ^ (j + 1 + 1)‖
        ≤ ((j + 1 : ℕ) : ℝ) * ((|k| / c ^ (j + 1 + 1)) * (‖u‖⁻¹ * ‖u - 1‖⁻¹ * (1 + ‖u‖)⁻¹)) := by
          gcongr
      _ = _ := by ring
  · filter_upwards [ae_restrict_mem measurableSet_upperHalf_aux] with u hu
    intro z hz
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    have hz0 := hne z hz u hu
    have hd : HasDerivAt (fun z : ℂ => conj u - z) (-1) z := by
      simpa using (hasDerivAt_id z).const_sub (conj u)
    have hp := (hd.pow (j + 1))
    have := (hasDerivAt_const z (m u / (conj u * (conj u - 1)))).div hp (pow_ne_zero _ hz0)
    refine HasDerivAt.congr_deriv this ?_
    simp only [Pi.pow_apply, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    field_simp
    ring

/-- Holomorphy of the kernel integral `z ↦ ∫_𝕌 R(z, ū) \overline{μ(u)} d²u` on `𝕌`, and its third derivative
`6 ∫_𝕌 \overline{μ(u)}/(ū - z)⁴ d²u` (TT:1228–1233). -/
theorem phiKernel_holomorphic {μ : ℂ → ℂ} {k : ℝ} (hμ : IsBeltramiCoeff μ upperHalf k) :
    DifferentiableOn ℂ (fun z => ∫ u in upperHalf, kernelRU z (conj u) * conj (μ u)) upperHalf ∧
      ∀ z ∈ upperHalf, iteratedDeriv 3 (fun z => ∫ u in upperHalf, kernelRU z (conj u) * conj (μ u)) z =
        6 * ∫ u in upperHalf, conj (μ u) / (conj u - z) ^ 4 := by
  have hm : AEStronglyMeasurable (fun u => conj (μ u)) (volume.restrict upperHalf) :=
    continuous_conj.comp_aestronglyMeasurable hμ.1
  have hb : ∀ᵐ u ∂(volume.restrict upperHalf), ‖conj (μ u)‖ ≤ k :=
    hμ.2.mono fun u hu => by simpa using hu
  set m : ℂ → ℂ := fun u => conj (μ u) with hmdef
  let W : ℕ → ℂ → ℂ := fun n z => ∫ u in upperHalf, m u / (conj u * (conj u - 1)) / (conj u - z) ^ n
  have hD (n : ℕ) (hn : 1 ≤ n) {z : ℂ} (hz : z ∈ upperHalf) : HasDerivAt (W n) ((n : ℂ) * W (n + 1) z) z :=
    (phiKernel_hasDerivAt hm hb n hn hz).2
  have hI (n : ℕ) (hn : 1 ≤ n) {z : ℂ} (hz : z ∈ upperHalf) :
      Integrable (fun u => m u / (conj u * (conj u - 1)) / (conj u - z) ^ (n + 1)) (volume.restrict upperHalf) :=
    (phiKernel_hasDerivAt hm hb n hn hz).1
  have hopen : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  set G : ℂ → ℂ := fun z => ∫ u in upperHalf, kernelRU z (conj u) * conj (μ u) with hG
  have hGW : G = fun z => z * (z - 1) * W 1 z := by
    funext z
    simp only [hG, W]
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards with u
    simp only [kernelRU, hmdef, pow_one, div_eq_mul_inv, mul_inv]
    ring
  let G1 : ℂ → ℂ := fun z => (2 * z - 1) * W 1 z + z * (z - 1) * W 2 z
  let G2 : ℂ → ℂ := fun z => 2 * W 1 z + 2 * (2 * z - 1) * W 2 z + 2 * (z * (z - 1)) * W 3 z
  let G3 : ℂ → ℂ := fun z => 6 * W 2 z + 6 * (2 * z - 1) * W 3 z + 6 * (z * (z - 1)) * W 4 z
  have hfd (z : ℂ) : HasDerivAt (fun z : ℂ => z * (z - 1)) (2 * z - 1) z := by
    convert (hasDerivAt_id' z).mul ((hasDerivAt_id' z).sub_const 1) using 1
    ring
  have hg1 (z : ℂ) (hz : z ∈ upperHalf) : HasDerivAt G (G1 z) z := by
    rw [hGW]
    have := (hfd z).mul (hD 1 le_rfl hz)
    refine HasDerivAt.congr_deriv this ?_
    simp [G1] <;> ring
  have hg2 (z : ℂ) (hz : z ∈ upperHalf) : HasDerivAt G1 (G2 z) z := by
    have h1 : HasDerivAt (fun y : ℂ => 2 * y - 1) 2 z := by
      simpa using ((hasDerivAt_id' z).const_mul (2 : ℂ)).sub_const 1
    have a1 := h1.mul (hD 1 le_rfl hz)
    have a2 := (hfd z).mul (hD 2 (by norm_num) hz)
    have := a1.add a2
    refine HasDerivAt.congr_deriv this ?_
    simp [G2] <;> ring
  have hg3 (z : ℂ) (hz : z ∈ upperHalf) : HasDerivAt G2 (G3 z) z := by
    have h1 : HasDerivAt (fun y : ℂ => 2 * y - 1) 2 z := by
      simpa using ((hasDerivAt_id' z).const_mul (2 : ℂ)).sub_const 1
    have a1 := (hD 1 le_rfl hz).const_mul (2 : ℂ)
    have a2 := (h1.const_mul (2 : ℂ)).mul (hD 2 (by norm_num) hz)
    have a3 := ((hfd z).const_mul (2 : ℂ)).mul (hD 3 (by norm_num) hz)
    have := (a1.add a2).add a3
    refine HasDerivAt.congr_deriv this ?_
    simp [G3] <;> ring
  have e1 : ∀ y ∈ upperHalf, deriv G y = G1 y := fun y hy => (hg1 y hy).deriv
  have e2 : ∀ y ∈ upperHalf, deriv (deriv G) y = G2 y := by
    intro y hy
    have : deriv G =ᶠ[𝓝 y] G1 := Filter.eventuallyEq_of_mem (hopen.mem_nhds hy) e1
    rw [this.deriv_eq]; exact (hg2 y hy).deriv
  have e3 : ∀ y ∈ upperHalf, deriv (deriv (deriv G)) y = G3 y := by
    intro y hy
    have : deriv (deriv G) =ᶠ[𝓝 y] G2 := Filter.eventuallyEq_of_mem (hopen.mem_nhds hy) e2
    rw [this.deriv_eq]; exact (hg3 y hy).deriv
  refine ⟨fun z hz => (hg1 z hz).differentiableAt.differentiableWithinAt, fun z hz => ?_⟩
  show iteratedDeriv 3 G z = _
  rw [iteratedDeriv_succ', iteratedDeriv_succ', iteratedDeriv_succ', iteratedDeriv_zero, e3 z hz]
  -- combine the three integrals
  have i2 : Integrable (fun u => m u / (conj u * (conj u - 1)) / (conj u - z) ^ 2) (volume.restrict upperHalf) :=
    hI 1 le_rfl hz
  have i3 : Integrable (fun u => m u / (conj u * (conj u - 1)) / (conj u - z) ^ 3) (volume.restrict upperHalf) :=
    hI 2 (by norm_num) hz
  have i4 : Integrable (fun u => m u / (conj u * (conj u - 1)) / (conj u - z) ^ 4) (volume.restrict upperHalf) :=
    hI 3 (by norm_num) hz
  have key : ∫ u in upperHalf, (6 * (m u / (conj u * (conj u - 1)) / (conj u - z) ^ 2) +
        6 * (2 * z - 1) * (m u / (conj u * (conj u - 1)) / (conj u - z) ^ 3) +
        6 * (z * (z - 1)) * (m u / (conj u * (conj u - 1)) / (conj u - z) ^ 4)) =
      G3 z := by
    have s1 := integral_add (i2.const_mul 6) (i3.const_mul (6 * (2 * z - 1)))
    have s2 := integral_add ((i2.const_mul 6).add (i3.const_mul (6 * (2 * z - 1)))) (i4.const_mul (6 * (z * (z - 1))))
    simp only [Pi.add_apply] at s2
    rw [s2, s1]
    simp only [G3, W, integral_const_mul]
  rw [← key]
  congr 1
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem hopen.measurableSet] with u hu
  have hu' : 0 < u.im := hu
  have ha0 : conj u ≠ 0 := fun h => by
    have h0 := (map_eq_zero (starRingEnd ℂ)).mp h
    rw [h0] at hu'; simp at hu'
  have ha1 : conj u - 1 ≠ 0 := fun h => by
    have : conj u = 1 := sub_eq_zero.mp h
    have := congrArg Complex.im this; simp at this; linarith
  have haz : conj u - z ≠ 0 := fun h => by
    have := congrArg Complex.im h; simp at this
    have hz' : 0 < z.im := hz
    linarith
  simp only [hmdef]
  field_simp
  ring

/-- `varPhi_holomorphic` for every bound `k ≥ 0`. -/
theorem varPhi_holomorphic_of_bounded {μ : ℂ → ℂ} {k : ℝ} (hk0 : 0 ≤ k) (hμ : IsBeltramiCoeff μ upperHalf k) :
    DifferentiableOn ℂ (varPhi μ) upperHalf ∧
      ∀ z ∈ upperHalf, iteratedDeriv 3 (varPhi μ) z = -(6 / π) * ∫ u in upperHalf, conj (μ u) / (conj u - z) ^ 4 := by
  have hopen : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  obtain ⟨hdiff, hder⟩ := phiKernel_holomorphic hμ
  have hvar : varPhi μ = fun z => (-(1 / π : ℝ) : ℂ) *
      ∫ u in upperHalf, kernelRU z (conj u) * conj (μ u) := by
    funext z
    rw [(eq_1_22_of_bounded hk0 hμ z).2]
    push_cast
    ring
  rw [hvar]
  refine ⟨hdiff.const_mul _, fun z hz => ?_⟩
  rw [iteratedDeriv_const_mul_field, hder z hz]
  push_cast
  ring

/-- (TT:1228–1233) `Φ[μ]` is holomorphic on `𝕌`, and `Φ[μ]_{zzz}(z) = -(6/π) ∬_𝕌 \overline{μ(u)}/(ū - z)⁴ d²u`. -/
theorem varPhi_holomorphic {μ : ℂ → ℂ} {k : ℝ} (hk0 : 0 ≤ k) (hk : k < 1) (hμ : IsBeltramiCoeff μ upperHalf k) :
    DifferentiableOn ℂ (varPhi μ) upperHalf ∧
      ∀ z ∈ upperHalf, iteratedDeriv 3 (varPhi μ) z = -(6 / π) * ∫ u in upperHalf, conj (μ u) / (conj u - z) ^ 4 := by
  exact varPhi_holomorphic_of_bounded hk0 hμ

/-- **(1.23)** (TT:1239). The projection `P : L∞(𝕌) → Ω^{-1,1}(𝕌)` in the model `𝕌`:
`(Pμ)(z) = -(3(z - z̄)²/π) ∬_𝕌 μ(u)/(u - z̄)⁴ d²u`. -/
def harmonicProjU (μ : ℂ → ℂ) (z : ℂ) : ℂ :=
  -(3 * (z - conj z) ^ 2 / π) * ∫ u in upperHalf, μ u / (u - conj z) ^ 4

/-- `μ ∈ Ω^{-1,1}(𝕌)` with `μ(z) = ((z - z̄)²/2) \overline{φ(z)}` (TT:1242): `φ` is holomorphic on `𝕌` with
`sup_𝕌 |(Im z)² φ(z)| < ∞` (i.e. `φ ∈ A∞(𝕌)`). -/
def IsHarmonicU (μ φ : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ φ upperHalf ∧ (∃ C, ∀ z ∈ upperHalf, ‖z.im ^ 2 * φ z‖ ≤ C) ∧
    ∀ z ∈ upperHalf, μ z = (z - conj z) ^ 2 / 2 * conj (φ z)

-- harmonicProjU_spec moved to Ch1/HalfPlaneBergman.lean (cycle)

theorem vf_zero_extension_coeff {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k)
    (hμ : IsBeltramiCoeff μ upperHalf k) :
    IsBeltramiCoeff (upperHalf.indicator μ) univ k := by
  have hm := measurableSet_upperHalf_aux
  constructor
  · rw [Measure.restrict_univ]
    exact (aestronglyMeasurable_indicator_iff hm).mpr hμ.1
  · rw [Measure.restrict_univ]
    have hb := (ae_restrict_iff' hm).mp hμ.2
    filter_upwards [hb] with u hu
    by_cases h : u ∈ upperHalf
    · rw [indicator_of_mem h]; exact hu h
    · rw [indicator_of_notMem h, norm_zero]; exact hk

/-- The actual parameter variation equals the Ahlfors transform of the zero extension. -/
theorem vf_varF_eq_ahVar {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k)
    (hμ : IsBeltramiCoeff μ upperHalf k) : varF μ = ahVar (upperHalf.indicator μ) := by
  funext z
  rw [(eq_1_22_of_bounded hk hμ z).1]
  unfold ahVar
  have hi : (fun u => upperHalf.indicator μ u * ahKer z u) =
      upperHalf.indicator (fun u => μ u * ahKer z u) := by
    funext u
    by_cases hu : u ∈ upperHalf <;> simp [indicator_apply, hu]
  rw [hi, integral_indicator measurableSet_upperHalf_aux]
  congr 1
  apply integral_congr_ae (Filter.Eventually.of_forall _)
  intro u
  unfold kernelRU ahKer
  ring

theorem vf_varF_lower_holomorphic {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k)
    (hμ : IsBeltramiCoeff μ upperHalf k) : DifferentiableOn ℂ (varF μ) lowerHalf := by
  rw [vf_varF_eq_ahVar hk hμ]
  apply QCV.qcv_ahVar_holomorphic hk (vf_zero_extension_coeff hk hμ)
    (isOpen_lt Complex.continuous_im continuous_const)
  intro u hu
  apply indicator_of_notMem
  intro hu'
  have h1 : u.im < 0 := hu
  have h2 : 0 < u.im := hu'
  linarith

theorem vf_normalizedCauchy_eq_ahVar (κ : ℂ → ℂ) : normalizedCauchyTOn univ κ = ahVar κ := by
  funext z
  unfold normalizedCauchyTOn ahVar
  rw [Measure.restrict_univ]
  simp_rw [← integral_const_mul]
  apply integral_congr_ae (Filter.Eventually.of_forall _)
  intro u
  unfold ahKer
  ring

/-- The actual upper-half-plane variation solves the inhomogeneous Cauchy equation weakly. -/
theorem vf_varF_weak_dzbar {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k)
    (hμ : IsBeltramiCoeff μ upperHalf k) {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    (∫ z, varF μ z * dzbar φ z) = -∫ z in upperHalf, μ z * φ z := by
  have h := GardinerLakic2000.thm3_7_d ⟨k, vf_zero_extension_coeff hk hμ⟩ hφ hc
  rw [vf_normalizedCauchy_eq_ahVar, ← vf_varF_eq_ahVar hk hμ] at h
  have hi : (fun z => upperHalf.indicator μ z * φ z) = upperHalf.indicator (fun z => μ z * φ z) := by
    funext z
    by_cases hz : z ∈ upperHalf <;> simp [indicator_apply, hz]
  rwa [hi, integral_indicator measurableSet_upperHalf_aux] at h

theorem vf_indicator_coeff {κ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k)
    (hκ : IsBeltramiCoeff κ univ k) {S : Set ℂ} (hS : MeasurableSet S) :
    IsBeltramiCoeff (S.indicator κ) univ k := by
  have hm : AEStronglyMeasurable κ volume := by simpa using hκ.1
  have hb : ∀ᵐ u : ℂ, ‖κ u‖ ≤ k := by simpa using hκ.2
  constructor
  · rw [Measure.restrict_univ]
    exact hm.indicator hS
  · rw [Measure.restrict_univ]
    filter_upwards [hb] with u hu
    by_cases hs : u ∈ S
    · rwa [indicator_of_mem hs]
    · rw [indicator_of_notMem hs, norm_zero]; exact hk

theorem vf_cutoff_memLp_four {κ : ℂ → ℂ} {k : ℝ}
    (hκ : IsBeltramiCoeff κ univ k) (R : ℝ) :
    MemLp ((closedBall (0 : ℂ) R).indicator κ) 4 volume := by
  letI : IsFiniteMeasure (volume.restrict (closedBall (0 : ℂ) R)) :=
    isFiniteMeasure_restrict.mpr measure_closedBall_lt_top.ne
  apply (memLp_indicator_iff_restrict measurableSet_closedBall).mpr
  have hm : AEStronglyMeasurable κ volume := by simpa using hκ.1
  have hb : ∀ᵐ u : ℂ, ‖κ u‖ ≤ k := by simpa using hκ.2
  exact MemLp.of_bound hm.restrict k (ae_restrict_of_ae hb)

/-- Locally, the normalized Ahlfors integral differs from an actual compact-support
Cauchy transform by a holomorphic function. -/
theorem vf_ahVar_local_cauchy {κ : ℂ → ℂ} {k R : ℝ} (hk : 0 ≤ k) (hR : 0 < R)
    (hκ : IsBeltramiCoeff κ univ k) :
    DifferentiableOn ℂ (fun z => ahVar κ z - cauchyT ((closedBall (0 : ℂ) R).indicator κ) z)
      (ball 0 R) := by
  let ν := (closedBall (0 : ℂ) R).indicator κ
  let η := (closedBall (0 : ℂ) R)ᶜ.indicator κ
  have hν : IsBeltramiCoeff ν univ k := vf_indicator_coeff hk hκ measurableSet_closedBall
  have hη : IsBeltramiCoeff η univ k := vf_indicator_coeff hk hκ measurableSet_closedBall.compl
  have hsplit : κ = fun u => (1 : ℂ) * ν u + η u := by
    funext u
    by_cases hu : u ∈ closedBall (0 : ℂ) R <;> simp [ν, η, indicator_apply, hu]
  have hv : ∀ z, ahVar κ z = ahVar ν z + ahVar η z := by
    intro z
    calc ahVar κ z = ahVar (fun u => (1 : ℂ) * ν u + η u) z := congrArg (fun q => ahVar q z) hsplit
         _ = _ := by simpa using ah_var_linear hν hη 1 z
  have hνp : MemLp ν (ENNReal.ofReal 4) := by simpa using vf_cutoff_memLp_four hκ R
  have hsupp : ∀ z : ℂ, R < ‖z‖ → ν z = 0 := by
    intro z hz
    exact indicator_of_notMem (by simpa using not_le.mpr hz) κ
  have ht : DifferentiableOn ℂ (ahVar η) (ball (0 : ℂ) R) := by
    apply QCV.qcv_ahVar_holomorphic hk hη isOpen_ball
    intro z hz
    exact indicator_of_notMem (by simpa using ball_subset_closedBall hz) κ
  have he : (fun z => ahVar κ z - cauchyT ν z) =
      (fun z => ahVar η z - cauchyT ν 0 - z * (cauchyT ν 1 - cauchyT ν 0)) := by
    funext z
    rw [hv z, ahC_ahVar_eq (by norm_num : (2 : ℝ) < 4) hR hνp hsupp z]
    ring
  change DifferentiableOn ℂ (fun z => ahVar κ z - cauchyT ν z) (ball 0 R)
  rw [he]
  exact (ht.sub_const _).sub (differentiableOn_id.mul_const _)

theorem vf_varF_local_cauchy {μ : ℂ → ℂ} {k R : ℝ} (hk : 0 ≤ k) (hR : 0 < R)
    (hμ : IsBeltramiCoeff μ upperHalf k) :
    DifferentiableOn ℂ (fun z => varF μ z -
      cauchyT ((closedBall (0 : ℂ) R).indicator (upperHalf.indicator μ)) z) (ball 0 R) := by
  rw [vf_varF_eq_ahVar hk hμ]
  exact vf_ahVar_local_cauchy hk hR (vf_zero_extension_coeff hk hμ)

/-- The precise remaining classical-regularity input: generalized L4 partials identify
the classical Cauchy derivative wherever real differentiability holds a.e. -/
theorem vf_cutoff_classical_dzbar_of_differentiable {κ : ℂ → ℂ} {k R : ℝ}
    (hκ : IsBeltramiCoeff κ univ k)
    (hd : ∀ᵐ z : ℂ, DifferentiableAt ℝ (cauchyT ((closedBall (0 : ℂ) R).indicator κ)) z) :
    ∀ᵐ z : ℂ, dzbar (cauchyT ((closedBall (0 : ℂ) R).indicator κ)) z =
      (closedBall (0 : ℂ) R).indicator κ z := by
  let ν := (closedBall (0 : ℂ) R).indicator κ
  have hνp : MemLp ν (ENNReal.ofReal 4) := by simpa using vf_cutoff_memLp_four hκ R
  have hs : Bornology.IsBounded (Function.support ν) := by
    apply isBounded_closedBall.subset
    intro z hz
    by_contra h
    exact hz (indicator_of_notMem h κ)
  obtain ⟨hgen, hbar, -⟩ := thm11_1 (by norm_num : (2 : ℝ) < 4) hνp hs
  obtain ⟨-, hx, hy⟩ := lemma9_2_isACL_of_genPartials isOpen_univ (by norm_num) hgen
  rw [Measure.restrict_univ] at hx hy
  filter_upwards [hd, hx, hy] with z hdz hxz hyz
  change dzbar (cauchyT ν) z = ν z
  rw [dzbar, ← partialX_eq_of_differentiableAt hdz, ← partialY_eq_of_differentiableAt hdz, hxz, hyz]
  exact hbar z

/-- A countable local reduction of the classical equation to real differentiability
of compact-support Cauchy transforms. This extra input is stated explicitly. -/
theorem vf_varF_dzbar_of_cutoff_differentiability {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k)
    (hμ : IsBeltramiCoeff μ upperHalf k)
    (hd : ∀ n : ℕ, ∀ᵐ z : ℂ, DifferentiableAt ℝ
      (cauchyT ((closedBall (0 : ℂ) (n + 1)).indicator (upperHalf.indicator μ))) z) :
    ∀ᵐ z : ℂ, dzbar (varF μ) z = upperHalf.indicator μ z := by
  let κ := upperHalf.indicator μ
  have hκ := vf_zero_extension_coeff hk hμ
  have hbar : ∀ n : ℕ, ∀ᵐ z : ℂ,
      dzbar (cauchyT ((closedBall (0 : ℂ) (n + 1)).indicator κ)) z =
        (closedBall (0 : ℂ) (n + 1)).indicator κ z :=
    fun n => vf_cutoff_classical_dzbar_of_differentiable hκ (hd n)
  filter_upwards [ae_all_iff.mpr hd, ae_all_iff.mpr hbar] with z hdz hbz
  obtain ⟨n, hn⟩ := exists_nat_gt ‖z‖
  have hR : 0 < (n : ℝ) + 1 := by positivity
  have hz : z ∈ ball (0 : ℂ) ((n : ℝ) + 1) := by
    rw [mem_ball_zero_iff]
    linarith
  let T := cauchyT ((closedBall (0 : ℂ) ((n : ℝ) + 1)).indicator κ)
  have hT : DifferentiableAt ℝ T z := hdz n
  have hc : DifferentiableAt ℂ (fun w => varF μ w - T w) z :=
    (vf_varF_local_cauchy hk hR hμ).differentiableAt (isOpen_ball.mem_nhds hz)
  have he : varF μ = (fun w => varF μ w - T w) + T := by funext w; simp
  have hder : dzbar (varF μ) z = dzbar (fun w => varF μ w - T w) z + dzbar T z := by
    conv_lhs => rw [he]
    simp only [dzbar, fderiv_add (hc.restrictScalars ℝ) hT, ContinuousLinearMap.add_apply]
    ring
  rw [hder, (cauchyRiemann_iff.mp hc).2, zero_add, hbz n]
  exact indicator_of_mem (ball_subset_closedBall hz) κ


/-- (TT:1242) `F[μ]_{z̄} = μ` on `𝕌` (a.e.), and `F[μ]` is holomorphic on the lower half-plane. -/
theorem varF_spec {μ : ℂ → ℂ} {k : ℝ} (hk0 : 0 ≤ k) (hk : k < 1) (hμ : IsBeltramiCoeff μ upperHalf k) :
    (∀ᵐ z ∂(volume.restrict upperHalf), dzbar (varF μ) z = μ z) ∧ DifferentiableOn ℂ (varF μ) lowerHalf := by
  have hκ := vf_zero_extension_coeff hk0 hμ
  have hd : ∀ n : ℕ, ∀ᵐ z : ℂ, DifferentiableAt ℝ
      (cauchyT ((closedBall (0 : ℂ) ((n : ℝ) + 1)).indicator (upperHalf.indicator μ))) z := by
    intro n
    apply mp_cauchy_differentiable_ae (vf_cutoff_memLp_four hκ ((n : ℝ) + 1))
    apply isBounded_closedBall.subset
    intro z hz
    by_contra h
    exact hz (indicator_of_notMem h (upperHalf.indicator μ))
  refine ⟨?_, vf_varF_lower_holomorphic hk0 hμ⟩
  have hbar := vf_varF_dzbar_of_cutoff_differentiability hk0 hμ hd
  filter_upwards [ae_restrict_of_ae hbar, self_mem_ae_restrict measurableSet_upperHalf_aux]
    with z hz hzU
  simpa only [indicator_of_mem hzU] using hz

/-- `𝕌(z, ε) = 𝕌 \ {|u - z| < ε}` (TT:1256). -/
def upperHalfPunct (z : ℂ) (ε : ℝ) : Set ℂ := upperHalf \ ball z ε

-- `lemma_1_12` moved to `Ch1/L112.lean` (2026-10-28).

-- `lemma_1_13` moved to `Ch1/L613.lean` (2026-10-28).

-- `remark_1_14` moved to `Ch1/L613.lean` (2026-10-28).

-- `cor_1_15` moved to `Ch1/L613.lean` (2026-10-28).

/-- `K_μ(u, v) = (w_μ)_u(u) (w_μ)_v(v)/(w_μ(u) - w_μ(v))²` (TT:1295). -/
def kernelK (μ : ℂ → ℂ) (u v : ℂ) : ℂ := dz (wU μ) u * dz (wU μ) v / (wU μ u - wU μ v) ^ 2

/-- `K_μ(u, v̄) = (w_μ)_u(u) \overline{(w_μ)_v(v)}/(w_μ(u) - \overline{w_μ(v)})²` (TT:1295). -/
def kernelKbar (μ : ℂ → ℂ) (u v : ℂ) : ℂ :=
  dz (wU μ) u * conj (dz (wU μ) v) / (wU μ u - conj (wU μ v)) ^ 2

/-- `K_μ(ū, v̄) = \overline{K_μ(u, v)}`, the kernel with both arguments conjugated, used in (1.25). (The kernels are
symmetric, `K_μ(v̄, u) = K_μ(u, v̄)`, which is how `K_μ(v̄, u)` and `K_μ(v, ū)` of (1.24)–(1.25) are written.) -/
def kernelKbarbar (μ : ℂ → ℂ) (u v : ℂ) : ℂ := conj (kernelK μ u v)

/-- The principal value `lim_{δ → 0} ∬_{𝕌 \ (B(a, δ) ∪ B(b, δ))} f`, removing disks around the two singular points
(junk `0` if the limit does not exist). -/
def pv2 (f : ℂ → ℂ) (a b : ℂ) : ℂ := limUnder (𝓝[>] (0 : ℝ)) fun δ => ∫ v in upperHalf \ (ball a δ ∪ ball b δ), f v

-- `eq_1_24` moved to `Ch1/Eq124General.lean` (2026-10-28).

-- `eq_1_25` moved to `Ch1/Eq124General.lean` (2026-10-28).

/-! ## The unit disk model -/

/-- The kernel `R(z, u) = (z + 1)(z + i)(z - 1)/((u - z)(u + 1)(u + i)(u - 1))` for the model `𝔻`, where `w_μ` fixes
`-1, -i, 1` (TT:1325). -/
def kernelRD (z u : ℂ) : ℂ := (z + 1) * (z + I) * (z - 1) / ((u - z) * (u + 1) * (u + I) * (u - 1))

/-- `w` is a q.c. self-map of `ℂ̄` with complex dilatation `m`, normalized at `0` by `w(0) = 0`, `w'(0) = 1`,
`w''(0) = 0`; `m` vanishes near `0`, so `w` is holomorphic there (TT:1330–1334). As in Model B, such maps are
`M ∘ W` with `W` a normalized plane solution and `M` Möbius. -/
def IsNormalizedAtZero (m : ℂ → ℂ) (w : ExtPlane → ExtPlane) : Prop :=
  ∃ M : ExtPlane → ExtPlane, IsMobius M ∧ ∃ W : ℂ → ℂ, IsNormalizedSolution W m ∧
    (∀ z : ℂ, w z = M (W z)) ∧ w extInf = M extInf ∧
    ∃ r > 0, ∃ f : ℂ → ℂ, (∀ z ∈ ball (0 : ℂ) r, w z = (f z : ExtPlane)) ∧ f 0 = 0 ∧ deriv f 0 = 1 ∧
      deriv (deriv f) 0 = 0

/-- The solution `v_{m}` normalized at `0` (junk `id` if none). -/
def vAtZero (m : ℂ → ℂ) : ExtPlane → ExtPlane :=
  if h : ∃ w, IsNormalizedAtZero m w then h.choose else id

theorem vz_plane_solution_unique {m W V : ℂ → ℂ}
    (hW : IsNormalizedSolution W m) (hV : IsNormalizedSolution V m) : W = V := by
  apply thm13_5_uniqueness_plane hW.1 hV.1 hW.2.1 hV.2.1 ?_
    hW.2.2.1 hW.2.2.2.1 hV.2.2.1 hV.2.2.2.1
  filter_upwards [hW.2.2.2.2, hV.2.2.2.2] with z hw hv using hw.trans hv.symm

/-- The explicit Möbius postcomposition realizing the three prescribed zero jets. -/
theorem vz_normalized_explicit {m W : ℂ → ℂ} (hW : IsNormalizedSolution W m)
    (hWa : AnalyticAt ℂ W 0) (ha : deriv W 0 ≠ 0) :
    IsNormalizedAtZero m (mobiusExt 1 0 (deriv (deriv W) 0 / (2 * deriv W 0))
      (deriv W 0) ∘ OnePoint.map W) := by
  let a := deriv W 0
  let b := deriv (deriv W) 0
  let c := b / (2 * a)
  have ha' : a ≠ 0 := ha
  have hW0 : W 0 = 0 := hW.2.2.1
  have hd : c * W 0 + a ≠ 0 := by simp only [hW0, mul_zero, zero_add]; exact ha'
  have hden : ∀ᶠ z in 𝓝 (0 : ℂ), c * W z + a ≠ 0 :=
    (hWa.continuousAt.const_mul c |>.add_const a).eventually_ne hd
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hden
  refine ⟨mobiusExt 1 0 c a, ⟨1, 0, c, a, by simpa using ha', rfl⟩,
    W, hW, fun z => rfl, rfl, r, hr, fun z => mobiusFn 1 0 c a (W z), ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact mobiusExt_coe (hball hz)
  · simp [mobiusFn, hW0]
  · have h := (mobius_comp_first_second (a := 1) (b := 0) hWa hd).1
    rw [h, hW0]
    dsimp only [a]
    simp only [one_mul, zero_mul, mul_zero, sub_zero, zero_add]
    field_simp
  · have h := (mobius_comp_first_second (a := 1) (b := 0) hWa hd).2
    rw [h, hW0]
    dsimp [a, b, c]
    field_simp
    <;> ring

theorem vz_normalized_representation {m W : ℂ → ℂ} {w : ExtPlane → ExtPlane}
    (hW : IsNormalizedSolution W m) (hWa : AnalyticAt ℂ W 0) (hw : IsNormalizedAtZero m w) :
    ∃ a b c d : ℂ, a * d - b * c ≠ 0 ∧
      (∀ z : ℂ, w z = mobiusExt a b c d (W z)) ∧ w extInf = mobiusExt a b c d extInf ∧ d ≠ 0 ∧
      mobiusFn a b c d (W 0) = 0 ∧ deriv (fun z => mobiusFn a b c d (W z)) 0 = 1 ∧
      deriv (deriv (fun z => mobiusFn a b c d (W z))) 0 = 0 := by
  obtain ⟨M, ⟨a, b, c, d, hdet, rfl⟩, V, hV, hfin, hinf, r, hr, f, hf, hf0, hf1, hf2⟩ := hw
  have hVW := vz_plane_solution_unique hV hW
  subst V
  have hW0 : W 0 = 0 := hW.2.2.1
  have hd : d ≠ 0 := by
    intro hd
    have he := (hfin 0).symm.trans (hf 0 (mem_ball_self hr))
    rw [hf0, hW0, mobiusExt_coe_of_eq_zero (by simp [hd])] at he
    exact OnePoint.infty_ne_coe (0 : ℂ) he
  have hden : ∀ᶠ z in 𝓝 (0 : ℂ), c * W z + d ≠ 0 :=
    (hWa.continuousAt.const_mul c |>.add_const d).eventually_ne (by simpa only [hW0, mul_zero, zero_add] using hd)
  have heq : (fun z => mobiusFn a b c d (W z)) =ᶠ[𝓝 (0 : ℂ)] f := by
    filter_upwards [hden, ball_mem_nhds (0 : ℂ) hr] with z hz hzr
    have he := (hfin z).symm.trans (hf z hzr)
    rw [mobiusExt_coe hz] at he
    exact OnePoint.coe_injective he
  exact ⟨a, b, c, d, hdet, hfin, hinf, hd, heq.self_of_nhds.trans hf0,
    heq.deriv_eq.trans hf1, heq.deriv.deriv_eq.trans hf2⟩

theorem vz_normalization_unique {m W : ℂ → ℂ} {w v : ExtPlane → ExtPlane}
    (hW : IsNormalizedSolution W m) (hWa : AnalyticAt ℂ W 0)
    (hw : IsNormalizedAtZero m w) (hv : IsNormalizedAtZero m v) : w = v := by
  obtain ⟨a, b, c, d, hdet, hfin, hinf, hd, h0, h1, h2⟩ := vz_normalized_representation hW hWa hw
  obtain ⟨a', b', c', d', hdet', hfin', hinf', hd', h0', h1', h2'⟩ := vz_normalized_representation hW hWa hv
  have he := normalized_mobius_comp_unique hWa hW.2.2.1 hd hd' h0 h1 h2 h0' h1' h2'
  funext p
  induction p using OnePoint.rec with
  | infty => rw [hinf, hinf', he]
  | coe z => rw [hfin, hfin', he]

/-- The actual choice in `vAtZero` equals the explicit normalized solution. -/
theorem vz_vAtZero_eq {m W : ℂ → ℂ} (hW : IsNormalizedSolution W m)
    (hWa : AnalyticAt ℂ W 0) (ha : deriv W 0 ≠ 0) :
    vAtZero m = mobiusExt 1 0 (deriv (deriv W) 0 / (2 * deriv W 0))
      (deriv W 0) ∘ OnePoint.map W := by
  have he := vz_normalized_explicit hW hWa ha
  have hex : ∃ w, IsNormalizedAtZero m w := ⟨_, he⟩
  have hs : IsNormalizedAtZero m (vAtZero m) := by
    unfold vAtZero
    rw [dite_eq_left hex]
    exact hex.choose_spec
  exact vz_normalization_unique hW hWa hs he

theorem vz_plane_holomorphic_on {m W : ℂ → ℂ} {U : Set ℂ}
    (hW : IsNormalizedSolution W m) (hU : IsOpen U) (hzero : ∀ z ∈ U, m z = 0) :
    DifferentiableOn ℂ W U := by
  obtain ⟨K, hK⟩ := hW.1
  have hKU := t3b_isKQC_restrict hK hU (subset_univ U)
  apply nx_differentiableOn_of_dilatation_zero hKU
  filter_upwards [ae_restrict_of_ae hW.2.2.2.2, ae_restrict_mem hU.measurableSet] with z hm hz
  rw [hm, hzero z hz]

theorem vz_vAtZero_eq_of_zero_on {m W : ℂ → ℂ} {U : Set ℂ}
    (hW : IsNormalizedSolution W m) (hU : IsOpen U) (h0 : (0 : ℂ) ∈ U)
    (hzero : ∀ z ∈ U, m z = 0) :
    vAtZero m = mobiusExt 1 0 (deriv (deriv W) 0 / (2 * deriv W 0))
      (deriv W 0) ∘ OnePoint.map W := by
  have hd := vz_plane_holomorphic_on hW hU hzero
  obtain ⟨K, hK⟩ := hW.1
  have hi : InjOn W U := hK.2.2.1.2.1.mono (subset_univ U)
  exact vz_vAtZero_eq hW (hd.analyticAt (hU.mem_nhds h0))
    (deriv_ne_zero_of_injOn hU hd hi h0)

theorem vz_scaled_coeff {κ : ℂ → ℂ} {k : ℝ} (hκ : IsBeltramiCoeff κ univ k) (t : ℂ) :
    IsBeltramiCoeff (fun u => t * κ u) univ (k * ‖t‖) := by
  refine ⟨hκ.1.const_mul t, ?_⟩
  filter_upwards [hκ.2] with u hu
  rw [norm_mul, mul_comm k]
  exact mul_le_mul_of_nonneg_left hu (norm_nonneg t)

theorem vz_scaled_hasDerivAt {κ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k)
    (hκ : IsBeltramiCoeff κ univ k) (z : ℂ) :
    HasDerivAt (fun t : ℂ => normalizedSolution (fun u => t * κ u) z) (ahVar κ z) 0 := by
  have hg0 : IsBeltramiCoeff (0 : ℂ → ℂ) univ 0 :=
    ⟨aestronglyMeasurable_zero, Filter.Eventually.of_forall fun u => by simp⟩
  have hf0 : IsNormalizedSolution id (0 : ℂ → ℂ) := by
    have h := QCV.qcv_ns_spec le_rfl zero_lt_one hg0
    rwa [bB_l_normalizedSolution_zero] at h
  have hlin : ∀ (a v₁ v₂ : ℂ), (fun u => (a • v₁ + v₂) * κ u) =ᵐ[volume]
      (fun u => a * (v₁ * κ u) + v₂ * κ u) := by
    intro a v₁ v₂
    exact Filter.Eventually.of_forall fun u => by simp only [smul_eq_mul]; ring
  obtain ⟨L, hL, hd⟩ := QCV.qcv_plane_hasFDerivAt (E := ℂ) (g₀ := (0 : ℂ → ℂ))
    (f₀ := id) (k := 0) le_rfl zero_lt_one hg0 hf0 (fun t u => t * κ u) hk
    (vz_scaled_coeff hκ) hlin z
  have h := hd.hasDerivAt
  simp only [Pi.zero_apply, zero_add] at h
  apply h.congr_deriv
  rw [hL 1, QCV.qcv_var_source le_rfl zero_lt_one hg0 hf0 (vz_scaled_coeff hκ 1)]
  have hdz : ∀ u, dz (id : ℂ → ℂ) u = 1 := by intro u; simp [dz]
  simp only [id_eq, hdz, one_pow, mul_one, one_mul, ahVar]

theorem vz_scaled_param_holomorphic {κ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k)
    (hκ : IsBeltramiCoeff κ univ k) (z : ℂ) :
    DifferentiableOn ℂ (fun t : ℂ => normalizedSolution (fun u => t * κ u) z)
      {t : ℂ | ‖t‖ * k < 1} := by
  have h0 : IsBeltramiCoeff (0 : ℂ → ℂ) univ 0 :=
    ⟨aestronglyMeasurable_zero, Filter.Eventually.of_forall fun u => by simp⟩
  intro t ht
  obtain ⟨L, hd, -⟩ := QCV.qcv_plane_two_param_hasFDerivAt hk le_rfl hκ h0
    (p₀ := (t, 0)) (by simpa using ht) z
  have hpair : DifferentiableAt ℂ (fun s : ℂ => (s, (0 : ℂ))) t := by fun_prop
  have h := hd.differentiableAt.comp t hpair
  simpa only [Function.comp_def, Pi.zero_apply, mul_zero, add_zero] using h.differentiableWithinAt

theorem vz_univalent_bound {F : ℂ → ℂ} (hd : DifferentiableOn ℂ F unitDisc)
    (hi : Function.Injective F) (h0 : F 0 = 0) {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    ‖F ζ‖ ≤ 4 * ‖F 2‖ * (‖ζ‖ / (1 - ‖ζ‖) ^ 2) := by
  have hout : F 2 ∉ F '' unitDisc := by
    rintro ⟨u, hu, he⟩
    have hu2 := hi he
    have hn := mem_ball_zero_iff.mp hu
    rw [hu2] at hn
    norm_num at hn
  have hq := koebe_quarter_of_not_mem hd hi.injOn h0 hout
  have hg := koebe_growth_scaled hd hi.injOn h0 hζ
  calc ‖F ζ‖ ≤ ‖deriv F 0‖ * ‖ζ‖ / (1 - ‖ζ‖) ^ 2 := hg
       _ = ‖deriv F 0‖ * (‖ζ‖ / (1 - ‖ζ‖) ^ 2) := by ring
       _ ≤ 4 * ‖F 2‖ * (‖ζ‖ / (1 - ‖ζ‖) ^ 2) := by gcongr

theorem vz_small_parameter {k : ℝ} (hk : 0 ≤ k) {t : ℂ}
    (ht : ‖t‖ < 1 / (k + 1)) : k * ‖t‖ < 1 := by
  rw [lt_div_iff₀ (by positivity)] at ht
  nlinarith [norm_nonneg t]

/-- Uniform spatial bounds on a small zero neighborhood justify parameter differentiation
of both normalization jets. -/
theorem vz_scaled_jets {κ : ℂ → ℂ} {k : ℝ} {U : Set ℂ} (hk : 0 ≤ k)
    (hκ : IsBeltramiCoeff κ univ k) (hU : IsOpen U) (h0 : (0 : ℂ) ∈ U)
    (hzero : ∀ z ∈ U, κ z = 0) :
    HasDerivAt (fun t : ℂ => deriv (normalizedSolution (fun u => t * κ u)) 0) (deriv (ahVar κ) 0) 0 ∧
      HasDerivAt (fun t : ℂ => deriv (deriv (normalizedSolution (fun u => t * κ u))) 0)
        (deriv (deriv (ahVar κ)) 0) 0 := by
  obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.mp hU 0 h0
  let W : ℂ → ℂ → ℂ := fun t z => normalizedSolution (fun u => t * κ u) z
  let r₀ := 1 / (k + 1)
  let r := r₀ / 2
  have hr₀ : 0 < r₀ := by dsimp [r₀]; positivity
  have hr : 0 < r := by dsimp [r]; positivity
  have hsmall : closedBall (0 : ℂ) r ⊆ ball 0 r₀ :=
    closedBall_subset_ball (by dsimp [r]; linarith)
  have htk : ∀ t ∈ ball (0 : ℂ) r₀, k * ‖t‖ < 1 :=
    fun t ht => vz_small_parameter hk (mem_ball_zero_iff.mp ht)
  have hspec : ∀ t ∈ ball (0 : ℂ) r₀, IsNormalizedSolution (W t) (fun u => t * κ u) := by
    intro t ht
    exact QCV.qcv_ns_spec (by positivity) (htk t ht) (vz_scaled_coeff hκ t)
  have hspace : ∀ t ∈ ball (0 : ℂ) r₀, DifferentiableOn ℂ (W t) U := by
    intro t ht
    exact vz_plane_holomorphic_on (hspec t ht) hU (fun z hz => by rw [hzero z hz, mul_zero])
  have hparam : ∀ z, DifferentiableOn ℂ (fun t => W t z) (ball (0 : ℂ) r₀) := by
    intro z
    exact (vz_scaled_param_holomorphic hk hκ z).mono (fun t ht => by
      show ‖t‖ * k < 1
      rw [mul_comm]
      exact htk t ht)
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) r).exists_bound_of_continuousOn
    ((hparam ((R : ℂ) * 2)).continuousOn.mono hsmall)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (mem_closedBall_self hr.le))
  have hM : ∀ t ∈ ball (0 : ℂ) r, ∀ z ∈ ball (0 : ℂ) (R / 2), ‖W t z‖ ≤ 8 * B := by
    intro t ht z hz
    have ht₀ := hsmall (ball_subset_closedBall ht)
    let G : ℂ → ℂ := fun ζ => W t ((R : ℂ) * ζ)
    have hGd : DifferentiableOn ℂ G unitDisc := by
      apply (hspace t ht₀).comp (differentiableOn_id.const_mul (R : ℂ))
      intro ζ hζ
      apply hRU
      have hn := mem_ball_zero_iff.mp hζ
      simp only [mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hR, id_eq]
      nlinarith
    obtain ⟨K, hK⟩ := (hspec t ht₀).1
    have hWi : Function.Injective (W t) := fun x y he => hK.2.2.1.2.1 (mem_univ _) (mem_univ _) he
    have hRn : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
    have hGi : Function.Injective G := fun x y he => mul_left_cancel₀ hRn (hWi he)
    have hG0 : G 0 = 0 := by simpa only [G, mul_zero] using (hspec t ht₀).2.2.1
    have hzhalf : ‖z / (R : ℂ)‖ < 1 / 2 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, div_lt_iff₀ hR]
      have hn := mem_ball_zero_iff.mp hz
      linarith
    have hb := vz_univalent_bound hGd hGi hG0 (hzhalf.trans (by norm_num : (1 / 2 : ℝ) < 1))
    have hm : ‖z / (R : ℂ)‖ / (1 - ‖z / (R : ℂ)‖) ^ 2 ≤ 2 := by
      calc _ ≤ (1 / 2 : ℝ) / (1 - 1 / 2) ^ 2 := QCV.qcv_mono_koebe
            (norm_nonneg (z / (R : ℂ))) hzhalf.le (by norm_num : (1 / 2 : ℝ) < 1)
           _ = 2 := by norm_num
    have hGt : ‖G 2‖ ≤ B := hB t (ball_subset_closedBall ht)
    have he : G (z / (R : ℂ)) = W t z := by simp [G, mul_div_cancel₀ _ hRn]
    rw [he] at hb
    calc ‖W t z‖ ≤ 4 * ‖G 2‖ * (‖z / (R : ℂ)‖ / (1 - ‖z / (R : ℂ)‖) ^ 2) := hb
         _ ≤ 4 * B * 2 := by gcongr
         _ = 8 * B := by ring
  have hspace' : ∀ t ∈ ball (0 : ℂ) r, DifferentiableOn ℂ (W t) (ball (0 : ℂ) (R / 2)) := by
    intro t ht
    exact (hspace t (hsmall (ball_subset_closedBall ht))).mono
      ((ball_subset_ball (by linarith)).trans hRU)
  have hparam' : ∀ z ∈ ball (0 : ℂ) (R / 2),
      DifferentiableOn ℂ (fun t => W t z) (ball (0 : ℂ) r) :=
    fun z _ => (hparam z).mono (ball_subset_closedBall.trans hsmall)
  have hV : (fun z => deriv (fun t => W t z) 0) = ahVar κ := by
    funext z
    exact (vz_scaled_hasDerivAt hk hκ z).deriv
  have h1 := QCV.qcv_param_hasDerivAt_iter 1 hr (half_pos hR) hspace' hparam' hM
  have h2 := QCV.qcv_param_hasDerivAt_iter 2 hr (half_pos hR) hspace' hparam' hM
  rw [hV] at h1 h2
  exact ⟨by simpa only [W, iteratedDeriv_one] using h1,
    by simpa only [W, iteratedDeriv_succ', iteratedDeriv_zero] using h2⟩

/-- Actual zero-jet-normalized variation: the correction to the plane variation is quadratic. -/
theorem vz_vAtZero_hasDerivAt {κ : ℂ → ℂ} {k : ℝ} {U : Set ℂ} (hk : 0 ≤ k)
    (hκ : IsBeltramiCoeff κ univ k) (hU : IsOpen U) (h0 : (0 : ℂ) ∈ U)
    (hzero : ∀ z ∈ U, κ z = 0) (z : ℂ) :
    HasDerivAt (fun t : ℂ => finPart (vAtZero (fun u => t * κ u) (z : ExtPlane)))
      (ahVar κ z - deriv (ahVar κ) 0 * z - deriv (deriv (ahVar κ)) 0 / 2 * z ^ 2) 0 := by
  let W : ℂ → ℂ → ℂ := fun t z => normalizedSolution (fun u => t * κ u) z
  let a : ℂ → ℂ := fun t => deriv (W t) 0
  let b : ℂ → ℂ := fun t => deriv (deriv (W t)) 0
  let c : ℂ → ℂ := fun t => b t / (2 * a t)
  have hW0 : W 0 = id := by
    simp only [W, zero_mul]
    exact bB_l_normalizedSolution_zero
  have ha0 : a 0 = 1 := by simp [a, hW0]
  have hb0 : b 0 = 0 := by simp [b, hW0]
  have hc0 : c 0 = 0 := by simp [c, hb0]
  obtain ⟨ha, hb⟩ := vz_scaled_jets hk hκ hU h0 hzero
  change HasDerivAt a (deriv (ahVar κ) 0) 0 at ha
  change HasDerivAt b (deriv (deriv (ahVar κ)) 0) 0 at hb
  have hc : HasDerivAt c (deriv (deriv (ahVar κ)) 0 / 2) 0 := by
    apply (hb.div (ha.const_mul 2) (by rw [ha0]; norm_num)).congr_deriv
    rw [ha0, hb0]
    ring
  have hw : HasDerivAt (fun t => W t z) (ahVar κ z) 0 := vz_scaled_hasDerivAt hk hκ z
  have hw0 : W 0 z = z := congrFun hW0 z
  have hd : HasDerivAt (fun t => c t * W t z + a t)
      (deriv (deriv (ahVar κ)) 0 / 2 * z + deriv (ahVar κ) 0) 0 := by
    apply ((hc.mul hw).add ha).congr_deriv
    rw [hc0, hw0]
    ring
  have hd0 : c 0 * W 0 z + a 0 ≠ 0 := by rw [hc0, ha0]; norm_num
  have hquot : HasDerivAt (fun t => W t z / (c t * W t z + a t))
      (ahVar κ z - deriv (ahVar κ) 0 * z - deriv (deriv (ahVar κ)) 0 / 2 * z ^ 2) 0 := by
    apply (hw.div hd hd0).congr_deriv
    rw [hc0, ha0, hw0]
    ring
  apply hquot.congr_of_eventuallyEq
  have hr : 0 < 1 / (k + 1) := by positivity
  filter_upwards [ball_mem_nhds (0 : ℂ) hr, hd.continuousAt.eventually_ne hd0] with t ht hden
  have htk := vz_small_parameter hk (mem_ball_zero_iff.mp ht)
  have hspec : IsNormalizedSolution (W t) (fun u => t * κ u) :=
    QCV.qcv_ns_spec (by positivity) htk (vz_scaled_coeff hκ t)
  have he := vz_vAtZero_eq_of_zero_on hspec hU h0 (fun u hu => by rw [hzero u hu, mul_zero])
  rw [he]
  change finPart (mobiusExt 1 0 (c t) (a t) ((W t z : ℂ) : ExtPlane)) = _
  rw [mobiusExt_coe hden, finPart_coe]
  simp [mobiusFn]

theorem vz_variation_of_zero_on {κ : ℂ → ℂ} {k : ℝ} {U : Set ℂ} (hk : 0 ≤ k)
    (hκ : IsBeltramiCoeff κ univ k) (hU : IsOpen U) (h0 : (0 : ℂ) ∈ U)
    (hzero : ∀ z ∈ U, κ z = 0) :
    let vdot := fun z : ℂ => deriv (fun t : ℂ => finPart (vAtZero (fun u => t * κ u) z)) 0
    DifferentiableOn ℂ vdot U ∧
      ∀ z ∈ U, iteratedDeriv 3 vdot z = -(6 / π) * ∫ u, κ u / (u - z) ^ 4 := by
  let A := deriv (ahVar κ) 0
  let B := deriv (deriv (ahVar κ)) 0 / 2
  have he : (fun z : ℂ => deriv (fun t : ℂ => finPart (vAtZero (fun u => t * κ u) z)) 0) =
      (fun z => ahVar κ z - A * z - B * z ^ 2) := by
    funext z
    exact (vz_vAtZero_hasDerivAt hk hκ hU h0 hzero z).deriv
  dsimp only
  rw [he]
  have hv := QCV.qcv_ahVar_holomorphic hk hκ hU hzero
  refine ⟨(hv.sub (by fun_prop)).sub (by fun_prop), ?_⟩
  intro z hz
  have hvc : ContDiffAt ℂ 3 (ahVar κ) z := (hv.analyticAt (hU.mem_nhds hz)).contDiffAt
  have hlin : ContDiffAt ℂ 3 (fun w : ℂ => A * w) z := by fun_prop
  have hquad : ContDiffAt ℂ 3 (fun w : ℂ => B * w ^ 2) z := by fun_prop
  rw [iteratedDeriv_fun_sub (hvc.sub hlin) hquad, iteratedDeriv_fun_sub hvc hlin]
  have hl3 : iteratedDeriv 3 (fun w : ℂ => A * w) z = 0 := by
    rw [iteratedDeriv_const_mul_field]
    simp [iteratedDeriv_succ', iteratedDeriv_zero]
  have hq3 : iteratedDeriv 3 (fun w : ℂ => B * w ^ 2) z = 0 := by
    rw [iteratedDeriv_const_mul_field]
    simp [iteratedDeriv_pow]
  rw [hl3, hq3, sub_zero, sub_zero]
  exact QCV.qcv_ahVar_iter3 hk hκ hU hzero hz

/-- **(1.26)** (TT:1328–1344).
- Hypotheses:
  - `f` is a q.c. map of `ℂ` with `f|𝔻 ∈ 𝒟`;
  - `μ` is a Beltrami differential supported on the quasidisk `Ω* = f(𝔻*)`;
  - `v_{tμ}` solves `(v_{tμ})_{z̄} = tμ (v_{tμ})_z` on `ℂ`, normalized by `v(0) = 0`, `v'(0) = 1`, `v''(0) = 0`.
- Then `v̇ = d/dt|_{t=0} v_{tμ}` is holomorphic on `Ω = f(𝔻)`, and
  `v̇_{zzz}(z) = -(6/π) ∬_{Ω*} μ(u)/(u - z)⁴ d²u`. -/
theorem eq_1_26 {f : ℂ → ℂ} (hf : f ∈ ClassD) (hfqc : IsQuasiconformal f univ ∧ f '' univ = univ)
    {μ : ℂ → ℂ} {k : ℝ} (hk0 : 0 ≤ k) (hk : k < 1) (hμ : IsBeltramiCoeff μ univ k)
    (hsupp : ∀ z, z ∉ f '' unitDiscExterior → μ z = 0) :
    let vdot := fun z : ℂ => deriv (fun t : ℂ => finPart (vAtZero (fun y => t * μ y) z)) 0
    DifferentiableOn ℂ vdot (f '' unitDisc) ∧
      ∀ z ∈ f '' unitDisc, iteratedDeriv 3 vdot z = -(6 / π) * ∫ u in f '' unitDiscExterior, μ u / (u - z) ^ 4 := by
  obtain ⟨K, hK⟩ := hfqc.1
  have hi : Function.Injective f := fun x y he => hK.2.2.1.2.1 (mem_univ _) (mem_univ _) he
  have hDo : IsOpen unitDisc := isOpen_ball
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hΩ := isOpen_image_of_isKQC (t3b_isKQC_restrict hK hDo (subset_univ _))
  have hΩs := isOpen_image_of_isKQC (t3b_isKQC_restrict hK hEo (subset_univ _))
  have hf0 : f 0 = 0 := hf.2.2.1
  have h0 : (0 : ℂ) ∈ f '' unitDisc := ⟨0, by simp [unitDisc], hf0⟩
  have hzero : ∀ u ∈ f '' unitDisc, μ u = 0 := by
    intro u hu
    apply hsupp u
    rintro ⟨x, hx, hxu⟩
    obtain ⟨y, hy, hyu⟩ := hu
    have he := hi (hxu.trans hyu.symm)
    subst x
    have hn := mem_ball_zero_iff.mp hy
    have hn' : 1 < ‖y‖ := hx
    linarith
  obtain ⟨hhol, hthird⟩ := vz_variation_of_zero_on hk0 hμ hΩ h0 hzero
  refine ⟨hhol, ?_⟩
  intro z hz
  rw [hthird z hz]
  congr 1
  have he : (fun u => μ u / (u - z) ^ 4) = (f '' unitDiscExterior).indicator (fun u => μ u / (u - z) ^ 4) := by
    funext u
    by_cases hu : u ∈ f '' unitDiscExterior
    · rw [indicator_of_mem hu]
    · rw [indicator_of_notMem hu, hsupp u hu, zero_div]
  conv_lhs => rw [he]
  rw [integral_indicator hΩs.measurableSet]

end TakhtajanTeo
