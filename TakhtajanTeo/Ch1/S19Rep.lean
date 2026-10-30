import TakhtajanTeo.Ch1.S19Mix
import TakhtajanTeo.Ch1.S13Cusp
import TakhtajanTeo.Ch1.S19Core
import TakhtajanTeo.Ch1.InvariantProjectionMixing
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.Analysis.Matrix.MeasurableSpace

/-!
# W-MIX stage 2, layer R: the right-regular representation of `SL(2, ℝ)` on `L²(Γ'\G)` (`s19r` prefix)

Approved definitions (leader, in principle):
- the Borel structure of `SL(2, ℝ)` as a subtype of `Matrix (Fin 2) (Fin 2) ℝ`;
- `s19rIwasawa (τ, θ) = g_τ k_θ`, `g_τ = [[√y, x/√y], [0, 1/√y]]` (`g_τ • i = τ = x + iy`), `k_θ` the rotation;
- `s19rMeasure`: the pushforward of `(Im τ)⁻² d²τ × dθ|_{[0, 2π)}` (Mathlib's `volume` on `ℍ`) under `s19rIwasawa`;
- `s19rDomain Γ = {g : C(g • i) ∈ fundDomain Γ}`, `C(τ) = (τ + i)/(τ - i)` the Cayley map `ℍ → 𝔻*` of `S13Cusp`.

No representation is defined: the right-regular action on `L²(μ|_D)` is the honest folded translate
`fold φ h g = ∑' γ : Γ', 1_D(γ g h) φ(γ g h)` (`Γ'` acts on the left, `D` a fundamental domain), and the packaged
`hrep` of `s19c_core_of_rep` is assembled from R1–R4 in the final proof.

Standing hypotheses on `(Γ, Γ')`: `Γ` cofinite, `Γ'` Fuchsian with `-1 ∈ Γ'` (harmless: `-1` acts trivially), and `Γ, Γ'` related through the Cayley map as in
`s13c_transfer_cover` (`hrel`, `hrel'`).
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real Matrix MatrixGroups UpperHalfPlane

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

/-- The Borel structure on `SL(2, ℝ)`, as a subtype of the `2 × 2` matrices. -/
instance s19rMeasurableSpace : MeasurableSpace SL(2, ℝ) :=
  inferInstanceAs (MeasurableSpace {A : Matrix (Fin 2) (Fin 2) ℝ // A.det = 1})

instance s19rBorelSpace : BorelSpace SL(2, ℝ) :=
  inferInstanceAs (BorelSpace {A : Matrix (Fin 2) (Fin 2) ℝ // A.det = 1})

/-- The Iwasawa parametrization `(τ, θ) ↦ g_τ k_θ` of `SL(2, ℝ)`, `g_τ • i = τ`. -/
def s19rIwasawa (p : ℍ × ℝ) : SL(2, ℝ) :=
  ⟨!![√p.1.im, p.1.re / √p.1.im; 0, 1 / √p.1.im], by
    have h := Real.sqrt_pos.mpr p.1.im_pos
    rw [Matrix.det_fin_two_of]
    field_simp
    simp⟩ *
  ⟨!![Real.cos p.2, -Real.sin p.2; Real.sin p.2, Real.cos p.2], by
    rw [Matrix.det_fin_two_of]
    nlinarith [Real.sin_sq_add_cos_sq p.2]⟩

/-- Haar measure of `SL(2, ℝ)` in Iwasawa coordinates: `(Im τ)⁻² d²τ dθ`, `θ ∈ [0, 2π)`. -/
def s19rMeasure : Measure SL(2, ℝ) :=
  Measure.map s19rIwasawa ((volume : Measure ℍ).prod (volume.restrict (Ico 0 (2 * π))))

/-- The fundamental domain of `Γ' ∋ -1` in `SL(2, ℝ)` above the chosen fundamental domain of `Γ` in `𝔻*`: `g • i` lies
over `F`, and the rotation angle of `g = g_τ k_θ` lies in `[0, π)` (second row `(sin θ, cos θ)/√y`), which cuts `±g`. -/
def s19rDomain (Γ : Subgroup SL2C) : Set SL(2, ℝ) :=
  {g | (((g • UpperHalfPlane.I : ℍ) : ℂ) + I) / (((g • UpperHalfPlane.I : ℍ) : ℂ) - I) ∈ fundDomain Γ ∧
    (0 < g 1 0 ∨ (g 1 0 = 0 ∧ 0 < g 1 1))}

/-- Entries of the Iwasawa matrix `g_τ k_θ`. -/
theorem s19r_iw_entries (p : ℍ × ℝ) :
    s19rIwasawa p 0 0 = √p.1.im * Real.cos p.2 + p.1.re / √p.1.im * Real.sin p.2 ∧
      s19rIwasawa p 0 1 = -(√p.1.im * Real.sin p.2) + p.1.re / √p.1.im * Real.cos p.2 ∧
      s19rIwasawa p 1 0 = 1 / √p.1.im * Real.sin p.2 ∧ s19rIwasawa p 1 1 = 1 / √p.1.im * Real.cos p.2 := by
  have key : (s19rIwasawa p : Matrix (Fin 2) (Fin 2) ℝ) =
      !![√p.1.im, p.1.re / √p.1.im; 0, 1 / √p.1.im] *
        !![Real.cos p.2, -Real.sin p.2; Real.sin p.2, Real.cos p.2] := rfl
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [key] <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The angle `θ(g) ∈ [0, 2π)` of `g = g_τ k_θ`: the argument of `g₁₁ + i g₁₀`. -/
theorem s19r_ang_mem (w : ℂ) :
    (if arg w < 0 then arg w + 2 * π else arg w) ∈ Ico (0 : ℝ) (2 * π) := by
  have h1 := neg_pi_lt_arg w
  have h2 := arg_le_pi w
  have hπ := Real.pi_pos
  split_ifs with h
  · exact ⟨by linarith, by linarith⟩
  · exact ⟨not_lt.mp h, by linarith⟩

/-- The entry maps of `SL(2, ℝ)` are measurable. -/
theorem s19r_meas_entry (i j : Fin 2) : Measurable fun g : SL(2, ℝ) => g i j :=
  (measurable_subtype_coe (p := fun A : Matrix (Fin 2) (Fin 2) ℝ => A.det = 1)).eval_matrix

/-- The Iwasawa map is measurable. -/
theorem s19r_iw_meas : Measurable s19rIwasawa := by
  have him : Measurable fun p : ℍ × ℝ => p.1.im :=
    Complex.measurable_im.comp (UpperHalfPlane.measurable_coe.comp measurable_fst)
  have hre : Measurable fun p : ℍ × ℝ => p.1.re :=
    Complex.measurable_re.comp (UpperHalfPlane.measurable_coe.comp measurable_fst)
  have hsq : Measurable fun p : ℍ × ℝ => √p.1.im := Real.continuous_sqrt.measurable.comp him
  have hc : Measurable fun p : ℍ × ℝ => Real.cos p.2 := Real.continuous_cos.measurable.comp measurable_snd
  have hs : Measurable fun p : ℍ × ℝ => Real.sin p.2 := Real.continuous_sin.measurable.comp measurable_snd
  have hmat : Measurable fun p : ℍ × ℝ => (s19rIwasawa p : Matrix (Fin 2) (Fin 2) ℝ) := by
    refine Measurable.of_eval_matrix _ fun i j => ?_
    fin_cases i <;> fin_cases j
    · convert (hsq.mul hc).add ((hre.div hsq).mul hs) using 1
      funext p
      exact (s19r_iw_entries p).1
    · convert (hsq.mul hs).neg.add ((hre.div hsq).mul hc) using 1
      funext p
      exact (s19r_iw_entries p).2.1
    · convert (measurable_const.div hsq).mul hs using 1
      funext p
      exact (s19r_iw_entries p).2.2.1
    · convert (measurable_const.div hsq).mul hc using 1
      funext p
      exact (s19r_iw_entries p).2.2.2
  exact hmat.subtype_mk

/-- The inverse of the Iwasawa map: `g ↦ (g • i, θ(g))`. -/
theorem s19r_inv_meas :
    Measurable fun g : SL(2, ℝ) => ((g • UpperHalfPlane.I : ℍ),
      (⟨if arg ((g 1 1 : ℂ) + (g 1 0 : ℂ) * I) < 0 then arg ((g 1 1 : ℂ) + (g 1 0 : ℂ) * I) + 2 * π
        else arg ((g 1 1 : ℂ) + (g 1 0 : ℂ) * I), s19r_ang_mem _⟩ : Ico (0 : ℝ) (2 * π))) := by
  have he : ∀ i j : Fin 2, Measurable fun g : SL(2, ℝ) => ((g i j : ℝ) : ℂ) := fun i j =>
    Complex.measurable_ofReal.comp (s19r_meas_entry i j)
  have hτ : Measurable fun g : SL(2, ℝ) => (g • UpperHalfPlane.I : ℍ) := by
    refine UpperHalfPlane.measurableEmbedding_coe.measurable_comp_iff.mp ?_
    have h : (fun g : SL(2, ℝ) => ((g • UpperHalfPlane.I : ℍ) : ℂ)) = fun g =>
        ((g 0 0 : ℂ) * I + (g 0 1 : ℂ)) / ((g 1 0 : ℂ) * I + (g 1 1 : ℂ)) := by
      funext g
      rw [UpperHalfPlane.coe_specialLinearGroup_apply]
      simp
    show Measurable fun g : SL(2, ℝ) => ((g • UpperHalfPlane.I : ℍ) : ℂ)
    rw [h]
    exact (((he 0 0).mul measurable_const).add (he 0 1)).div (((he 1 0).mul measurable_const).add (he 1 1))
  have hw : Measurable fun g : SL(2, ℝ) => arg ((g 1 1 : ℂ) + (g 1 0 : ℂ) * I) :=
    Complex.measurable_arg.comp ((he 1 1).add ((he 1 0).mul measurable_const))
  refine hτ.prodMk (Measurable.subtype_mk ?_)
  exact Measurable.ite (measurableSet_lt hw measurable_const) (hw.add measurable_const) hw

/-- `g_τ k_θ • i = τ`. -/
theorem s19r_iw_smul (τ : ℍ) (θ : ℝ) : (s19rIwasawa (τ, θ) • UpperHalfPlane.I : ℍ) = τ := by
  obtain ⟨e00, e01, e10, e11⟩ := s19r_iw_entries (τ, θ)
  simp only at e00 e01 e10 e11
  have hy := τ.im_pos
  have hs0 : 0 < √τ.im := Real.sqrt_pos.mpr hy
  have hsc : ((√τ.im : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs0.ne'
  have hsq : ((√τ.im : ℝ) : ℂ) * ((√τ.im : ℝ) : ℂ) = (τ.im : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hy.le]
  have hexp : ((Real.cos θ : ℝ) : ℂ) + ((Real.sin θ : ℝ) : ℂ) * I = exp (θ * I) := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have he0 : exp ((θ : ℂ) * I) ≠ 0 := Complex.exp_ne_zero _
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [Algebra.algebraMap_self, RingHom.id_apply, UpperHalfPlane.coe_I]
  rw [e00, e01, e10, e11]
  have hnum : (((√τ.im * Real.cos θ + τ.re / √τ.im * Real.sin θ : ℝ) : ℂ) * I +
      ((-(√τ.im * Real.sin θ) + τ.re / √τ.im * Real.cos θ : ℝ) : ℂ)) =
      ((√τ.im : ℝ) * I + (τ.re : ℂ) / (√τ.im : ℝ)) * exp (θ * I) := by
    rw [← hexp]
    push_cast
    linear_combination (-((√τ.im : ℝ) : ℂ) * Complex.sin (θ : ℂ)) * Complex.I_sq
  have hden : (((1 / √τ.im * Real.sin θ : ℝ) : ℂ) * I + ((1 / √τ.im * Real.cos θ : ℝ) : ℂ)) =
      exp (θ * I) / (√τ.im : ℝ) := by
    rw [← hexp]
    push_cast
    field_simp
    ring
  rw [hnum, hden, div_eq_iff (div_ne_zero he0 hsc)]
  have hτ : (τ : ℂ) = (τ.re : ℂ) + (τ.im : ℂ) * I := (Complex.re_add_im (τ : ℂ)).symm
  rw [hτ, ← hsq]
  field_simp
  ring

/-- The angle of `g_τ k_θ` is `θ`, for `θ ∈ [0, 2π)`. -/
theorem s19r_iw_ang (τ : ℍ) {θ : ℝ} (hθ : θ ∈ Ico (0 : ℝ) (2 * π)) :
    (if arg (((s19rIwasawa (τ, θ) 1 1 : ℝ) : ℂ) + ((s19rIwasawa (τ, θ) 1 0 : ℝ) : ℂ) * I) < 0 then
        arg (((s19rIwasawa (τ, θ) 1 1 : ℝ) : ℂ) + ((s19rIwasawa (τ, θ) 1 0 : ℝ) : ℂ) * I) + 2 * π
      else arg (((s19rIwasawa (τ, θ) 1 1 : ℝ) : ℂ) + ((s19rIwasawa (τ, θ) 1 0 : ℝ) : ℂ) * I)) = θ := by
  have hπ := Real.pi_pos
  obtain ⟨e00, e01, e10, e11⟩ := s19r_iw_entries (τ, θ)
  simp only at e00 e01 e10 e11
  have hy := τ.im_pos
  have hs0 : 0 < √τ.im := Real.sqrt_pos.mpr hy
  have hsc : ((√τ.im : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs0.ne'
  have hsq : ((√τ.im : ℝ) : ℂ) * ((√τ.im : ℝ) : ℂ) = (τ.im : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hy.le]
  have hexp : ((Real.cos θ : ℝ) : ℂ) + ((Real.sin θ : ℝ) : ℂ) * I = exp (θ * I) := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have he0 : exp ((θ : ℂ) * I) ≠ 0 := Complex.exp_ne_zero _
  have hw : ((s19rIwasawa (τ, θ) 1 1 : ℝ) : ℂ) + ((s19rIwasawa (τ, θ) 1 0 : ℝ) : ℂ) * I =
      ((1 / √τ.im : ℝ) : ℂ) * exp (θ * I) := by
    rw [e10, e11, ← hexp]
    push_cast
    ring
  have harg : arg (((s19rIwasawa (τ, θ) 1 1 : ℝ) : ℂ) + ((s19rIwasawa (τ, θ) 1 0 : ℝ) : ℂ) * I) =
      toIocMod Real.two_pi_pos (-π) θ := by
    rw [hw, Complex.arg_real_mul _ (by positivity), Complex.arg_exp_mul_I]
  rw [harg]
  rcases le_or_gt θ π with h | h
  · have ht : toIocMod Real.two_pi_pos (-π) θ = θ :=
      (toIocMod_eq_self _).mpr ⟨by linarith [hθ.1], by linarith⟩
    rw [ht, if_neg (not_lt.mpr hθ.1)]
  · have ht : toIocMod Real.two_pi_pos (-π) θ = θ - 2 * π :=
      (toIocMod_eq_iff _).mpr ⟨⟨by linarith, by linarith [hθ.2]⟩, 1, by simp⟩
    rw [ht, if_pos (by linarith [hθ.2])]
    ring

/-- Every `g ∈ SL(2, ℝ)` is `g_τ k_θ` with `τ = g • i` and `θ` its angle. -/
theorem s19r_iw_right (g : SL(2, ℝ)) :
    s19rIwasawa ((g • UpperHalfPlane.I : ℍ),
      (if arg ((g 1 1 : ℂ) + (g 1 0 : ℂ) * I) < 0 then arg ((g 1 1 : ℂ) + (g 1 0 : ℂ) * I) + 2 * π
        else arg ((g 1 1 : ℂ) + (g 1 0 : ℂ) * I))) = g := by
  have hπ := Real.pi_pos
  obtain ⟨θf, hθf⟩ : ∃ θf : SL(2, ℝ) → ℝ, θf = fun g =>
      if arg ((g 1 1 : ℂ) + (g 1 0 : ℂ) * I) < 0 then arg ((g 1 1 : ℂ) + (g 1 0 : ℂ) * I) + 2 * π
        else arg ((g 1 1 : ℂ) + (g 1 0 : ℂ) * I) := ⟨_, rfl⟩
  have hcs : ∀ g : SL(2, ℝ), (g 1 1 : ℂ) + (g 1 0 : ℂ) * I ≠ 0 →
      Real.cos (θf g) = g 1 1 / ‖(g 1 1 : ℂ) + (g 1 0 : ℂ) * I‖ ∧
        Real.sin (θf g) = g 1 0 / ‖(g 1 1 : ℂ) + (g 1 0 : ℂ) * I‖ := by
    intro g hw
    have h1 := Complex.cos_arg hw
    have h2 := Complex.sin_arg ((g 1 1 : ℂ) + (g 1 0 : ℂ) * I)
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
      Complex.I_im, Complex.add_im, Complex.mul_im] at h1 h2
    rw [hθf]
    simp only
    split_ifs
    · rw [Real.cos_add_two_pi, Real.sin_add_two_pi, h1, h2]
      constructor <;> ring
    · rw [h1, h2]
      constructor <;> ring
  have key : s19rIwasawa ((g • UpperHalfPlane.I : ℍ), θf g) = g := by
    have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
      have h := g.2
      rw [Matrix.det_fin_two] at h
      exact h
    have hw0 : ((g 1 1 : ℝ) : ℂ) + ((g 1 0 : ℝ) : ℂ) * I ≠ 0 := by
      intro h
      have h1 := congrArg Complex.re h
      have h2 := congrArg Complex.im h
      simp at h1 h2
      rw [h1, h2] at hdet
      linarith
    obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = ‖((g 1 1 : ℝ) : ℂ) + ((g 1 0 : ℝ) : ℂ) * I‖ := ⟨_, rfl⟩
    have hs0 : 0 < s := by rw [hsdef]; exact norm_pos_iff.mpr hw0
    have hss : s * s = g 1 0 ^ 2 + g 1 1 ^ 2 := by
      rw [hsdef, ← sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_add_mul_I]
      ring
    obtain ⟨u, hudef⟩ : ∃ u : ℝ, u = s⁻¹ := ⟨_, rfl⟩
    have hu : s * u = 1 := by rw [hudef]; exact mul_inv_cancel₀ hs0.ne'
    have hu0 : 0 ≤ u := by rw [hudef]; exact inv_nonneg.mpr hs0.le
    have huinv : u⁻¹ = s := by rw [hudef, inv_inv]
    obtain ⟨hcos, hsin⟩ := hcs g hw0
    rw [← hsdef, div_eq_mul_inv, ← hudef] at hcos hsin
    -- `g • i = p + q i` with `p = (ac + bd) u²`, `q = u²`
    have hA : (g 0 0 * g 1 0 + g 0 1 * g 1 1) * (u * u) * g 1 0 + u * u * g 1 1 = g 0 0 := by
      linear_combination (-(u ^ 2 * g 1 1)) * hdet - (g 0 0 * u ^ 2) * hss + g 0 0 * (u * s + 1) * hu
    have hB : (g 0 0 * g 1 0 + g 0 1 * g 1 1) * (u * u) * g 1 1 - u * u * g 1 0 = g 0 1 := by
      linear_combination (g 1 0 * u ^ 2) * hdet - (g 0 1 * u ^ 2) * hss + g 0 1 * (u * s + 1) * hu
    have hD : ((g 1 0 : ℝ) : ℂ) * I + ((g 1 1 : ℝ) : ℂ) ≠ 0 := fun h => hw0 (by rw [add_comm]; exact h)
    have hτ : ((g • UpperHalfPlane.I : ℍ) : ℂ) =
        (((g 0 0 * g 1 0 + g 0 1 * g 1 1) * (u * u) : ℝ) : ℂ) + ((u * u : ℝ) : ℂ) * I := by
      rw [UpperHalfPlane.coe_specialLinearGroup_apply]
      simp only [Algebra.algebraMap_self, RingHom.id_apply, UpperHalfPlane.coe_I]
      rw [div_eq_iff hD]
      calc ((g 0 0 : ℝ) : ℂ) * I + ((g 0 1 : ℝ) : ℂ) =
          (((g 0 0 * g 1 0 + g 0 1 * g 1 1) * (u * u) * g 1 0 + u * u * g 1 1 : ℝ) : ℂ) * I +
            (((g 0 0 * g 1 0 + g 0 1 * g 1 1) * (u * u) * g 1 1 - u * u * g 1 0 : ℝ) : ℂ) := by rw [hA, hB]
        _ = _ := by
          push_cast
          linear_combination (-((u : ℂ) * u * (g 1 0 : ℂ))) * Complex.I_sq
    have hy : (g • UpperHalfPlane.I : ℍ).im = u * u := by
      have h := congrArg Complex.im hτ
      simpa using h
    have hx : (g • UpperHalfPlane.I : ℍ).re = (g 0 0 * g 1 0 + g 0 1 * g 1 1) * (u * u) := by
      have h := congrArg Complex.re hτ
      simpa using h
    have hsqy : √(g • UpperHalfPlane.I : ℍ).im = u := by rw [hy]; exact Real.sqrt_mul_self hu0
    obtain ⟨e00, e01, e10, e11⟩ := s19r_iw_entries ((g • UpperHalfPlane.I : ℍ), θf g)
    simp only at e00 e01 e10 e11
    rw [hsqy, hx, hcos, hsin] at e00 e01
    rw [hsqy, hsin] at e10
    rw [hsqy, hcos] at e11
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    fin_cases i <;> fin_cases j
    · show s19rIwasawa ((g • UpperHalfPlane.I : ℍ), θf g) 0 0 = g 0 0
      rw [e00, div_eq_mul_inv, huinv]
      linear_combination ((g 0 0 * g 1 0 + g 0 1 * g 1 1) * g 1 0 * u ^ 2 + g 0 0 * (u * s + 1)) * hu
        - (u ^ 2 * g 1 1) * hdet - (g 0 0 * u ^ 2) * hss
    · show s19rIwasawa ((g • UpperHalfPlane.I : ℍ), θf g) 0 1 = g 0 1
      rw [e01, div_eq_mul_inv, huinv]
      linear_combination ((g 0 0 * g 1 0 + g 0 1 * g 1 1) * g 1 1 * u ^ 2 + g 0 1 * (u * s + 1)) * hu
        + (g 1 0 * u ^ 2) * hdet - (g 0 1 * u ^ 2) * hss
    · show s19rIwasawa ((g • UpperHalfPlane.I : ℍ), θf g) 1 0 = g 1 0
      rw [e10, one_div, huinv]
      linear_combination g 1 0 * hu
    · show s19rIwasawa ((g • UpperHalfPlane.I : ℍ), θf g) 1 1 = g 1 1
      rw [e11, one_div, huinv]
      linear_combination g 1 1 * hu
  rw [hθf] at key
  exact key

/-- **R1a.** The Iwasawa map is a measurable embedding of `ℍ × [0, 2π)` onto `SL(2, ℝ)`. -/
theorem s19r_iwasawa_embedding :
    MeasurableEmbedding (fun p : ℍ × Ico (0 : ℝ) (2 * π) => s19rIwasawa (p.1, p.2)) ∧
      range (fun p : ℍ × Ico (0 : ℝ) (2 * π) => s19rIwasawa (p.1, p.2)) = univ := by
  have hπ := Real.pi_pos
  obtain ⟨θf, hθf⟩ : ∃ θf : SL(2, ℝ) → ℝ, θf = fun g =>
      if arg ((g 1 1 : ℂ) + (g 1 0 : ℂ) * I) < 0 then arg ((g 1 1 : ℂ) + (g 1 0 : ℂ) * I) + 2 * π
        else arg ((g 1 1 : ℂ) + (g 1 0 : ℂ) * I) := ⟨_, rfl⟩
  have hθm : ∀ g, θf g ∈ Ico (0 : ℝ) (2 * π) := fun g => by rw [hθf]; exact s19r_ang_mem _
  obtain ⟨ι, hι⟩ : ∃ ι : SL(2, ℝ) → ℍ × Ico (0 : ℝ) (2 * π),
      ι = fun g => ((g • UpperHalfPlane.I : ℍ), ⟨θf g, hθm g⟩) := ⟨_, rfl⟩
  have hιm : Measurable ι := by
    subst hι hθf
    exact s19r_inv_meas
  have hleft : ∀ p : ℍ × Ico (0 : ℝ) (2 * π), ι (s19rIwasawa (p.1, p.2)) = p := by
    rintro ⟨τ, θ, hθ⟩
    rw [hι]
    refine Prod.ext (s19r_iw_smul τ θ) (Subtype.ext ?_)
    show θf (s19rIwasawa (τ, θ)) = θ
    rw [hθf]
    exact s19r_iw_ang τ hθ
  have hright : ∀ g : SL(2, ℝ), s19rIwasawa ((ι g).1, (ι g).2) = g := by
    intro g
    rw [hι]
    show s19rIwasawa ((g • UpperHalfPlane.I : ℍ), θf g) = g
    rw [hθf]
    exact s19r_iw_right g
  have hrange : range (fun p : ℍ × Ico (0 : ℝ) (2 * π) => s19rIwasawa (p.1, p.2)) = univ :=
    eq_univ_of_forall fun g => ⟨ι g, hright g⟩
  refine ⟨MeasurableEmbedding.of_measurable_inverse
    (s19r_iw_meas.comp (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd)))
    (by rw [hrange]; exact MeasurableSet.univ) hιm hleft, hrange⟩

/-- The Iwasawa map is `2π`-periodic in `θ`. -/
theorem s19r_iw_periodic (τ : ℍ) (θ : ℝ) : s19rIwasawa (τ, θ + 2 * π) = s19rIwasawa (τ, θ) := by
  obtain ⟨a1, a2, a3, a4⟩ := s19r_iw_entries (τ, θ + 2 * π)
  obtain ⟨b1, b2, b3, b4⟩ := s19r_iw_entries (τ, θ)
  simp only [Real.cos_add_two_pi, Real.sin_add_two_pi] at a1 a2 a3 a4 b1 b2 b3 b4
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  fin_cases i <;> fin_cases j
  · exact a1.trans b1.symm
  · exact a2.trans b2.symm
  · exact a3.trans b3.symm
  · exact a4.trans b4.symm

/-- `g_τ k_θ · k_φ = g_τ k_{θ + φ}` (`k_φ = g_i k_φ`). -/
theorem s19r_iw_mul_rot (τ : ℍ) (θ φ : ℝ) :
    s19rIwasawa (τ, θ) * s19rIwasawa (UpperHalfPlane.I, φ) = s19rIwasawa (τ, θ + φ) := by
  obtain ⟨a1, a2, a3, a4⟩ := s19r_iw_entries (τ, θ)
  obtain ⟨b1, b2, b3, b4⟩ := s19r_iw_entries (UpperHalfPlane.I, φ)
  obtain ⟨c1, c2, c3, c4⟩ := s19r_iw_entries (τ, θ + φ)
  simp only [UpperHalfPlane.I_im, UpperHalfPlane.I_re, Real.sqrt_one, zero_div, div_one, one_mul,
    zero_mul, add_zero, zero_add] at a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4
  simp only [Real.cos_add, Real.sin_add] at c1 c2 c3 c4
  have hm : ∀ i j : Fin 2, (s19rIwasawa (τ, θ) * s19rIwasawa (UpperHalfPlane.I, φ)) i j =
      s19rIwasawa (τ, θ) i 0 * s19rIwasawa (UpperHalfPlane.I, φ) 0 j +
        s19rIwasawa (τ, θ) i 1 * s19rIwasawa (UpperHalfPlane.I, φ) 1 j := fun i j => by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [hm]
  fin_cases i <;> fin_cases j
  · show s19rIwasawa (τ, θ) 0 0 * s19rIwasawa (UpperHalfPlane.I, φ) 0 0 +
      s19rIwasawa (τ, θ) 0 1 * s19rIwasawa (UpperHalfPlane.I, φ) 1 0 = s19rIwasawa (τ, θ + φ) 0 0
    rw [a1, a2, b1, b3, c1]
    ring
  · show s19rIwasawa (τ, θ) 0 0 * s19rIwasawa (UpperHalfPlane.I, φ) 0 1 +
      s19rIwasawa (τ, θ) 0 1 * s19rIwasawa (UpperHalfPlane.I, φ) 1 1 = s19rIwasawa (τ, θ + φ) 0 1
    rw [a1, a2, b2, b4, c2]
    ring
  · show s19rIwasawa (τ, θ) 1 0 * s19rIwasawa (UpperHalfPlane.I, φ) 0 0 +
      s19rIwasawa (τ, θ) 1 1 * s19rIwasawa (UpperHalfPlane.I, φ) 1 0 = s19rIwasawa (τ, θ + φ) 1 0
    rw [a3, a4, b1, b3, c3]
    ring
  · show s19rIwasawa (τ, θ) 1 0 * s19rIwasawa (UpperHalfPlane.I, φ) 0 1 +
      s19rIwasawa (τ, θ) 1 1 * s19rIwasawa (UpperHalfPlane.I, φ) 1 1 = s19rIwasawa (τ, θ + φ) 1 1
    rw [a3, a4, b2, b4, c4]
    ring

/-- Left multiplication by a fixed matrix is measurable on `SL(2, ℝ)`. -/
theorem s19r_mul_left_meas (h : SL(2, ℝ)) : Measurable fun g : SL(2, ℝ) => h * g := by
  have hmat : Measurable fun g : SL(2, ℝ) => ((h * g : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) := by
    refine Measurable.of_eval_matrix _ fun i j => ?_
    have hc : (fun g : SL(2, ℝ) => ((h * g : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) i j) =
        fun g => h i 0 * g 0 j + h i 1 * g 1 j := by
      funext g
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    rw [hc]
    exact (measurable_const.mul (s19r_meas_entry 0 j)).add (measurable_const.mul (s19r_meas_entry 1 j))
  exact hmat.subtype_mk

/-- The angle map is measurable. -/
theorem s19r_ang_meas : Measurable fun g : SL(2, ℝ) =>
    if arg ((g 1 1 : ℂ) + (g 1 0 : ℂ) * I) < 0 then arg ((g 1 1 : ℂ) + (g 1 0 : ℂ) * I) + 2 * π
      else arg ((g 1 1 : ℂ) + (g 1 0 : ℂ) * I) := by
  have he : ∀ i j : Fin 2, Measurable fun g : SL(2, ℝ) => ((g i j : ℝ) : ℂ) := fun i j =>
    Complex.measurable_ofReal.comp (s19r_meas_entry i j)
  have hw : Measurable fun g : SL(2, ℝ) => arg ((g 1 1 : ℂ) + (g 1 0 : ℂ) * I) :=
    Complex.measurable_arg.comp ((he 1 1).add ((he 1 0).mul measurable_const))
  exact Measurable.ite (measurableSet_lt hw measurable_const) (hw.add measurable_const) hw

/-- **Left Iwasawa cocycle.** `h g_τ k_θ = g_{h τ} k_{A(τ) + θ}` with `A` measurable. -/
theorem s19r_left_decomp (h : SL(2, ℝ)) :
    ∃ A : ℍ → ℝ, Measurable A ∧ ∀ τ θ, h * s19rIwasawa (τ, θ) = s19rIwasawa (h • τ, A τ + θ) := by
  refine ⟨fun τ => (if arg (((h * s19rIwasawa (τ, 0)) 1 1 : ℂ) + ((h * s19rIwasawa (τ, 0)) 1 0 : ℂ) * I) < 0 then
      arg (((h * s19rIwasawa (τ, 0)) 1 1 : ℂ) + ((h * s19rIwasawa (τ, 0)) 1 0 : ℂ) * I) + 2 * π
    else arg (((h * s19rIwasawa (τ, 0)) 1 1 : ℂ) + ((h * s19rIwasawa (τ, 0)) 1 0 : ℂ) * I)), ?_, ?_⟩
  · exact s19r_ang_meas.comp ((s19r_mul_left_meas h).comp (s19r_iw_meas.comp (measurable_id.prodMk measurable_const)))
  · intro τ θ
    have h1 : s19rIwasawa (τ, θ) = s19rIwasawa (τ, 0) * s19rIwasawa (UpperHalfPlane.I, θ) := by
      rw [s19r_iw_mul_rot, zero_add]
    have h2 := s19r_iw_right (h * s19rIwasawa (τ, 0))
    have h3 : ((h * s19rIwasawa (τ, 0)) • UpperHalfPlane.I : ℍ) = h • τ := by
      rw [mul_smul, s19r_iw_smul]
    rw [h3] at h2
    rw [h1, ← mul_assoc]
    conv_lhs => rw [← h2, s19r_iw_mul_rot]

/-- A `2π`-periodic function has shift-invariant integral over `[0, 2π)`. -/
theorem s19r_shift {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hper : ∀ θ, f (θ + 2 * π) = f θ) (a : ℝ) :
    ∫⁻ θ in Ico 0 (2 * π), f (a + θ) = ∫⁻ θ in Ico 0 (2 * π), f θ := by
  have hπ := Real.pi_pos
  haveI : Fact (0 < 2 * π) := ⟨by positivity⟩
  have hP : Function.Periodic f (2 * π) := hper
  have hcirc : ∀ t : ℝ, ∫⁻ θ in Ioc t (t + 2 * π), f θ = ∫⁻ b : AddCircle (2 * π), hP.lift b := by
    intro t
    rw [← AddCircle.lintegral_preimage (T := 2 * π) (t := t)]
    simp only [Function.Periodic.lift_coe]
  have htr : ∫⁻ θ in Ioc 0 (2 * π), f (a + θ) = ∫⁻ θ in Ioc a (a + 2 * π), f θ := by
    rw [← lintegral_indicator measurableSet_Ioc, ← lintegral_indicator measurableSet_Ioc]
    calc ∫⁻ θ, (Ioc 0 (2 * π)).indicator (fun θ => f (a + θ)) θ
        = ∫⁻ θ, (Ioc a (a + 2 * π)).indicator f (a + θ) := by
          congr 1
          funext θ
          by_cases hθ : θ ∈ Ioc 0 (2 * π)
          · have : a + θ ∈ Ioc a (a + 2 * π) := ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
            rw [indicator_of_mem hθ, indicator_of_mem this]
          · have : a + θ ∉ Ioc a (a + 2 * π) := fun h' => hθ ⟨by linarith [h'.1], by linarith [h'.2]⟩
            rw [indicator_of_notMem hθ, indicator_of_notMem this]
      _ = ∫⁻ θ, (Ioc a (a + 2 * π)).indicator f θ :=
          lintegral_add_left_eq_self (μ := volume) ((Ioc a (a + 2 * π)).indicator f) a
  rw [setLIntegral_congr Ico_ae_eq_Ioc, setLIntegral_congr Ico_ae_eq_Ioc, htr, hcirc a]
  have h0 := hcirc 0
  rw [zero_add] at h0
  exact h0.symm

/-- Right multiplication by a fixed matrix is measurable on `SL(2, ℝ)`. -/
theorem s19r_mul_right_meas (h : SL(2, ℝ)) : Measurable fun g : SL(2, ℝ) => g * h := by
  have hmat : Measurable fun g : SL(2, ℝ) => ((g * h : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) := by
    refine Measurable.of_eval_matrix _ fun i j => ?_
    have hc : (fun g : SL(2, ℝ) => ((g * h : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) i j) =
        fun g => g i 0 * h 0 j + g i 1 * h 1 j := by
      funext g
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    rw [hc]
    exact ((s19r_meas_entry i 0).mul measurable_const).add ((s19r_meas_entry i 1).mul measurable_const)
  exact hmat.subtype_mk

/-- The orbit map `g ↦ g • i` is measurable. -/
theorem s19r_smul_meas : Measurable fun g : SL(2, ℝ) => (g • UpperHalfPlane.I : ℍ) :=
  s19r_inv_meas.fst

/-- A slice of the Iwasawa measure after a `θ`-shift: `|{θ ∈ [0,2π) : g_τ k_{a+θ} ∈ S}| = |{θ : g_τ k_θ ∈ S}|`. -/
theorem s19r_slice_shift {S : Set SL(2, ℝ)} (hS : MeasurableSet S) (τ : ℍ) (a : ℝ) :
    (volume.restrict (Ico (0 : ℝ) (2 * π))) {θ | s19rIwasawa (τ, a + θ) ∈ S} =
      (volume.restrict (Ico (0 : ℝ) (2 * π))) {θ | s19rIwasawa (τ, θ) ∈ S} := by
  have hm : Measurable fun θ : ℝ => s19rIwasawa (τ, θ) :=
    s19r_iw_meas.comp (measurable_const.prodMk measurable_id)
  have hF : Measurable fun θ : ℝ => S.indicator (1 : SL(2, ℝ) → ℝ≥0∞) (s19rIwasawa (τ, θ)) :=
    (measurable_one.indicator hS).comp hm
  have h1 : MeasurableSet {θ : ℝ | s19rIwasawa (τ, a + θ) ∈ S} :=
    (hm.comp (measurable_const.add measurable_id)) hS
  have h2 : MeasurableSet {θ : ℝ | s19rIwasawa (τ, θ) ∈ S} := hm hS
  rw [← lintegral_indicator_one h1, ← lintegral_indicator_one h2]
  have e1 : ({θ : ℝ | s19rIwasawa (τ, a + θ) ∈ S}.indicator (1 : ℝ → ℝ≥0∞)) =
      fun θ => S.indicator (1 : SL(2, ℝ) → ℝ≥0∞) (s19rIwasawa (τ, a + θ)) := by
    funext θ
    by_cases hθ : s19rIwasawa (τ, a + θ) ∈ S
    · rw [indicator_of_mem (show θ ∈ {θ : ℝ | s19rIwasawa (τ, a + θ) ∈ S} from hθ), indicator_of_mem hθ]
      rfl
    · rw [indicator_of_notMem (show θ ∉ {θ : ℝ | s19rIwasawa (τ, a + θ) ∈ S} from hθ), indicator_of_notMem hθ]
  have e2 : ({θ : ℝ | s19rIwasawa (τ, θ) ∈ S}.indicator (1 : ℝ → ℝ≥0∞)) =
      fun θ => S.indicator (1 : SL(2, ℝ) → ℝ≥0∞) (s19rIwasawa (τ, θ)) := by
    funext θ
    by_cases hθ : s19rIwasawa (τ, θ) ∈ S
    · rw [indicator_of_mem (show θ ∈ {θ : ℝ | s19rIwasawa (τ, θ) ∈ S} from hθ), indicator_of_mem hθ]
      rfl
    · rw [indicator_of_notMem (show θ ∉ {θ : ℝ | s19rIwasawa (τ, θ) ∈ S} from hθ), indicator_of_notMem hθ]
  rw [e1, e2]
  exact s19r_shift hF (fun θ => by simp only [s19r_iw_periodic]) a

/-- **Left invariance** of `s19rMeasure`. -/
theorem s19r_left_inv (h : SL(2, ℝ)) : Measure.map (h * ·) s19rMeasure = s19rMeasure := by
  obtain ⟨A, -, hdec⟩ := s19r_left_decomp h
  ext S hS
  have hL := s19r_mul_left_meas h
  rw [Measure.map_apply hL hS]
  show (Measure.map s19rIwasawa ((volume : Measure ℍ).prod (volume.restrict (Ico 0 (2 * π)))))
      ((h * ·) ⁻¹' S) = (Measure.map s19rIwasawa ((volume : Measure ℍ).prod (volume.restrict (Ico 0 (2 * π))))) S
  rw [Measure.map_apply s19r_iw_meas (hL hS), Measure.map_apply s19r_iw_meas hS,
    Measure.prod_apply (s19r_iw_meas (hL hS)), Measure.prod_apply (s19r_iw_meas hS)]
  have hG : Measurable fun τ : ℍ => (volume.restrict (Ico (0 : ℝ) (2 * π))) (Prod.mk τ ⁻¹' (s19rIwasawa ⁻¹' S)) :=
    measurable_measure_prodMk_left (s19r_iw_meas hS)
  have hslice : ∀ τ : ℍ, (volume.restrict (Ico (0 : ℝ) (2 * π))) (Prod.mk τ ⁻¹' (s19rIwasawa ⁻¹' ((h * ·) ⁻¹' S))) =
      (volume.restrict (Ico (0 : ℝ) (2 * π))) (Prod.mk (h • τ) ⁻¹' (s19rIwasawa ⁻¹' S)) := by
    intro τ
    have e : Prod.mk τ ⁻¹' (s19rIwasawa ⁻¹' ((h * ·) ⁻¹' S)) = {θ | s19rIwasawa (h • τ, A τ + θ) ∈ S} := by
      ext θ
      simp only [mem_preimage, mem_setOf_eq]
      rw [hdec]
    rw [e, s19r_slice_shift hS]
    rfl
  simp_rw [hslice]
  have hsm : ∀ τ : ℍ, h • τ = (Matrix.SpecialLinearGroup.mapGL ℝ h) • τ := fun τ => rfl
  simp_rw [hsm]
  exact (measurePreserving_smul (Matrix.SpecialLinearGroup.mapGL ℝ h) (volume : Measure ℍ)).lintegral_comp hG

/-- **Right invariance under rotations**: `μ (S k_φ⁻¹) = μ S`. -/
theorem s19r_rot_inv (φ : ℝ) :
    Measure.map (· * s19rIwasawa (UpperHalfPlane.I, φ)) s19rMeasure = s19rMeasure := by
  ext S hS
  have hR := s19r_mul_right_meas (s19rIwasawa (UpperHalfPlane.I, φ))
  rw [Measure.map_apply hR hS]
  show (Measure.map s19rIwasawa ((volume : Measure ℍ).prod (volume.restrict (Ico 0 (2 * π)))))
      ((· * s19rIwasawa (UpperHalfPlane.I, φ)) ⁻¹' S) =
    (Measure.map s19rIwasawa ((volume : Measure ℍ).prod (volume.restrict (Ico 0 (2 * π))))) S
  rw [Measure.map_apply s19r_iw_meas (hR hS), Measure.map_apply s19r_iw_meas hS,
    Measure.prod_apply (s19r_iw_meas (hR hS)), Measure.prod_apply (s19r_iw_meas hS)]
  refine lintegral_congr fun τ => ?_
  have e : Prod.mk τ ⁻¹' (s19rIwasawa ⁻¹' ((· * s19rIwasawa (UpperHalfPlane.I, φ)) ⁻¹' S)) =
      {θ | s19rIwasawa (τ, φ + θ) ∈ S} := by
    ext θ
    simp only [mem_preimage, mem_setOf_eq]
    rw [s19r_iw_mul_rot, add_comm]
  rw [e, s19r_slice_shift hS]
  rfl

/-- **Orbit formula**: `∫ φ(g • i) dμ = 2π ∫_ℍ φ`. -/
theorem s19r_orbit {φ : ℍ → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ g, φ (g • UpperHalfPlane.I) ∂s19rMeasure = ENNReal.ofReal (2 * π) * ∫⁻ τ, φ τ := by
  have hπ := Real.pi_pos
  show ∫⁻ g, φ (g • UpperHalfPlane.I) ∂(Measure.map s19rIwasawa
      ((volume : Measure ℍ).prod (volume.restrict (Ico 0 (2 * π))))) = _
  rw [lintegral_map (f := fun g : SL(2, ℝ) => φ (g • UpperHalfPlane.I)) (hφ.comp s19r_smul_meas) s19r_iw_meas]
  have e : (fun p : ℍ × ℝ => φ (s19rIwasawa p • UpperHalfPlane.I)) = fun p => φ p.1 := by
    funext p
    rw [show p = (p.1, p.2) from rfl, s19r_iw_smul]
  rw [e, lintegral_prod (fun p : ℍ × ℝ => φ p.1) (hφ.comp measurable_fst).aemeasurable]
  simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ico, sub_zero]
  rw [lintegral_mul_const _ hφ, mul_comm]

/-- `s19rMeasure` is σ-finite (the pushforward along the measurable embedding of R1a). -/
theorem s19r_sigma : SigmaFinite s19rMeasure := by
  have hπ := Real.pi_pos
  obtain ⟨hemb, -⟩ := s19r_iwasawa_embedding
  have hs : MeasurableSet (Ico (0 : ℝ) (2 * π)) := measurableSet_Ico
  haveI : IsFiniteMeasure (Measure.comap ((↑) : Ico (0 : ℝ) (2 * π) → ℝ) volume) := by
    constructor
    rw [Measure.comap_apply _ Subtype.val_injective (fun t ht => hs.subtype_image ht) _ MeasurableSet.univ,
      image_univ, Subtype.range_coe, Real.volume_Ico]
    exact ENNReal.ofReal_lt_top
  have hν : (volume : Measure ℍ).prod (volume.restrict (Ico 0 (2 * π))) =
      Measure.map (Prod.map id ((↑) : Ico (0 : ℝ) (2 * π) → ℝ))
        ((volume : Measure ℍ).prod (Measure.comap ((↑) : Ico (0 : ℝ) (2 * π) → ℝ) volume)) := by
    rw [← Measure.map_prod_map _ _ measurable_id measurable_subtype_coe, Measure.map_id,
      map_comap_subtype_coe hs]
  show SigmaFinite (Measure.map s19rIwasawa ((volume : Measure ℍ).prod (volume.restrict (Ico 0 (2 * π)))))
  rw [hν, Measure.map_map s19r_iw_meas (measurable_id.prodMap measurable_subtype_coe)]
  exact hemb.sigmaFinite_map

/-- Nonempty open sets of `ℍ` have positive hyperbolic area. -/
theorem s19r_vol_pos {U : Set ℍ} (hU : IsOpen U) (hne : U.Nonempty) : 0 < (volume : Measure ℍ) U := by
  rw [UpperHalfPlane.volume_eq_lintegral]
  have hf : Measurable fun z : ℂ => ((((1 : NNReal) / ‖z.im‖₊) ^ 2 : NNReal) : ℝ≥0∞) := by fun_prop
  have hs : IsOpen (((↑) : ℍ → ℂ) '' U) := UpperHalfPlane.isOpenEmbedding_coe.isOpenMap U hU
  rw [lintegral_pos_iff_support hf, Measure.restrict_apply (measurableSet_support hf)]
  have hsub : ((↑) : ℍ → ℂ) '' U ⊆ Function.support fun z : ℂ => ((((1 : NNReal) / ‖z.im‖₊) ^ 2 : NNReal) : ℝ≥0∞) := by
    rintro _ ⟨τ, -, rfl⟩
    have h0 : (0 : ℝ) < (τ : ℂ).im := τ.im_pos
    have h1 : ‖(τ : ℂ).im‖₊ ≠ 0 := by
      rw [ne_eq, nnnorm_eq_zero]
      exact h0.ne'
    simpa [Function.mem_support] using τ.im_pos.ne'
  rw [inter_eq_self_of_subset_right hsub]
  exact hs.measure_pos _ (hne.image _)

/-- A compact set `K₀ = {g : g • i ∈ B̄(i, 1)}` with nonempty interior and `0 < μ K₀ < ∞`. -/
theorem s19r_K0 : ∃ K₀ : TopologicalSpace.PositiveCompacts SL(2, ℝ),
    0 < s19rMeasure K₀ ∧ s19rMeasure K₀ < ∞ := by
  have hπ := Real.pi_pos
  have hP := UpperHalfPlane.isProperMap_smul_I
  have hcont : Continuous fun g : SL(2, ℝ) => (g • UpperHalfPlane.I : ℍ) := hP.continuous
  obtain ⟨C, hC⟩ : ∃ C : Set ℍ, C = Metric.closedBall UpperHalfPlane.I 1 := ⟨_, rfl⟩
  have hCc : IsCompact C := by rw [hC]; exact isCompact_closedBall _ _
  have hK : IsCompact ((fun g : SL(2, ℝ) => (g • UpperHalfPlane.I : ℍ)) ⁻¹' C) := hP.isCompact_preimage hCc
  have hUo : IsOpen ((fun g : SL(2, ℝ) => (g • UpperHalfPlane.I : ℍ)) ⁻¹' Metric.ball UpperHalfPlane.I 1) :=
    Metric.isOpen_ball.preimage hcont
  have hUK : (fun g : SL(2, ℝ) => (g • UpperHalfPlane.I : ℍ)) ⁻¹' Metric.ball UpperHalfPlane.I 1 ⊆
      (fun g : SL(2, ℝ) => (g • UpperHalfPlane.I : ℍ)) ⁻¹' C := by
    rw [hC]
    exact preimage_mono Metric.ball_subset_closedBall
  have h1U : (1 : SL(2, ℝ)) ∈ (fun g : SL(2, ℝ) => (g • UpperHalfPlane.I : ℍ)) ⁻¹' Metric.ball UpperHalfPlane.I 1 := by
    show (1 : SL(2, ℝ)) • UpperHalfPlane.I ∈ Metric.ball UpperHalfPlane.I 1
    rw [one_smul]
    exact Metric.mem_ball_self one_pos
  refine ⟨⟨⟨_, hK⟩, ⟨1, interior_maximal hUK hUo h1U⟩⟩, ?_⟩
  have hCm : MeasurableSet C := hCc.isClosed.measurableSet
  have hμ : s19rMeasure ((fun g : SL(2, ℝ) => (g • UpperHalfPlane.I : ℍ)) ⁻¹' C) =
      ENNReal.ofReal (2 * π) * (volume : Measure ℍ) C := by
    have h := s19r_orbit (φ := C.indicator 1) (measurable_one.indicator hCm)
    have e : (fun g : SL(2, ℝ) => C.indicator (1 : ℍ → ℝ≥0∞) (g • UpperHalfPlane.I)) =
        ((fun g : SL(2, ℝ) => (g • UpperHalfPlane.I : ℍ)) ⁻¹' C).indicator 1 := by
      funext g
      by_cases hg : (g • UpperHalfPlane.I : ℍ) ∈ C
      · rw [indicator_of_mem hg, indicator_of_mem (show g ∈ (fun g : SL(2, ℝ) => (g • UpperHalfPlane.I : ℍ)) ⁻¹' C
          from hg)]
        rfl
      · rw [indicator_of_notMem hg, indicator_of_notMem (show g ∉ (fun g : SL(2, ℝ) => (g • UpperHalfPlane.I : ℍ)) ⁻¹' C
          from hg)]
    rw [e, lintegral_indicator_one (hCm.preimage s19r_smul_meas), lintegral_indicator_one hCm] at h
    exact h
  show 0 < s19rMeasure ((fun g : SL(2, ℝ) => (g • UpperHalfPlane.I : ℍ)) ⁻¹' C) ∧
    s19rMeasure ((fun g : SL(2, ℝ) => (g • UpperHalfPlane.I : ℍ)) ⁻¹' C) < ∞
  rw [hμ]
  have hpos : 0 < (volume : Measure ℍ) C := by
    refine lt_of_lt_of_le (s19r_vol_pos (U := Metric.ball UpperHalfPlane.I 1) Metric.isOpen_ball
      ⟨UpperHalfPlane.I, Metric.mem_ball_self one_pos⟩) ?_
    rw [hC]
    exact measure_mono Metric.ball_subset_closedBall
  exact ⟨ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (by positivity)).ne' hpos.ne',
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hCc.measure_lt_top⟩

/-- **Right invariance** of `s19rMeasure`. By Haar uniqueness `μ(· h⁻¹) = c(h) μ` with `c` multiplicative;
`c = 1` on rotations (θ-shifts), on unipotents (`a₂ n_x = n_{4x} a₂`, `n_{4x} = n_x⁴`) and on diagonals
(`w a_s = a_{1/s} w`, `a_s a_{1/s} = 1`), and `g = n_x a_{√y} k_θ`. -/
theorem s19r_right_inv (h : SL(2, ℝ)) : Measure.map (· * h) s19rMeasure = s19rMeasure := by
  haveI : SigmaFinite s19rMeasure := s19r_sigma
  haveI : Measure.IsMulLeftInvariant s19rMeasure := ⟨s19r_left_inv⟩
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → ℝ))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℝ))
  haveI : LocallyCompactSpace SL(2, ℝ) :=
    Matrix.SpecialLinearGroup.isClosedEmbedding_val.locallyCompactSpace
  haveI : SecondCountableTopology SL(2, ℝ) :=
    Matrix.SpecialLinearGroup.isClosedEmbedding_val.isEmbedding.secondCountableTopology
  obtain ⟨K₀, hK0, hK0'⟩ := s19r_K0
  have hK0ne : s19rMeasure K₀ ≠ 0 := hK0.ne'
  have hK0top : s19rMeasure K₀ ≠ ∞ := hK0'.ne
  -- the scalar factor of a right translate
  have hsc : ∀ g : SL(2, ℝ), ∃ c : ℝ≥0∞, Measure.map (· * g) s19rMeasure = c • s19rMeasure := by
    intro g
    haveI : SigmaFinite (Measure.map (· * g) s19rMeasure) :=
      (Homeomorph.mulRight g).measurableEmbedding.sigmaFinite_map
    haveI : Measure.IsMulLeftInvariant (Measure.map (· * g) s19rMeasure) := ⟨fun a => by
      rw [Measure.map_map (s19r_mul_left_meas a) (s19r_mul_right_meas g),
        show ((a * ·) ∘ (· * g)) = ((· * g) ∘ (a * ·)) from funext fun x => (mul_assoc a x g).symm,
        ← Measure.map_map (s19r_mul_right_meas g) (s19r_mul_left_meas a), s19r_left_inv]⟩
    have h1 := Measure.haarMeasure_unique (Measure.map (· * g) s19rMeasure) K₀
    have h2 := Measure.haarMeasure_unique s19rMeasure K₀
    have h3 : (s19rMeasure K₀)⁻¹ • s19rMeasure = Measure.haarMeasure K₀ := by
      calc (s19rMeasure K₀)⁻¹ • s19rMeasure
          = (s19rMeasure K₀)⁻¹ • (s19rMeasure K₀ • Measure.haarMeasure K₀) :=
            congrArg (fun m => (s19rMeasure K₀)⁻¹ • m) h2
        _ = Measure.haarMeasure K₀ := by rw [smul_smul, ENNReal.inv_mul_cancel hK0ne hK0top, one_smul]
    refine ⟨Measure.map (· * g) s19rMeasure K₀ * (s19rMeasure K₀)⁻¹, ?_⟩
    calc Measure.map (· * g) s19rMeasure = Measure.map (· * g) s19rMeasure K₀ • Measure.haarMeasure K₀ := h1
      _ = Measure.map (· * g) s19rMeasure K₀ • ((s19rMeasure K₀)⁻¹ • s19rMeasure) := by rw [h3]
      _ = _ := by rw [smul_smul]
  choose c hc using hsc
  have hev : ∀ g, Measure.map (· * g) s19rMeasure K₀ = c g * s19rMeasure K₀ := fun g => by
    rw [hc g, Measure.smul_apply, smul_eq_mul]
  have hcancel : ∀ x y : ℝ≥0∞, x * s19rMeasure K₀ = y * s19rMeasure K₀ → x = y := fun x y hxy =>
    (ENNReal.mul_left_inj hK0ne hK0top).mp hxy
  have hfix : ∀ g, Measure.map (· * g) s19rMeasure = s19rMeasure → c g = 1 := fun g hg =>
    hcancel _ _ (by rw [← hev, hg, one_mul])
  have hmul : ∀ g₁ g₂, c (g₁ * g₂) = c g₁ * c g₂ := by
    intro g₁ g₂
    have e : Measure.map (· * (g₁ * g₂)) s19rMeasure = (c g₁ * c g₂) • s19rMeasure := by
      rw [show (fun x : SL(2, ℝ) => x * (g₁ * g₂)) = (· * g₂) ∘ (· * g₁) from
        funext fun x => (mul_assoc x g₁ g₂).symm,
        ← Measure.map_map (s19r_mul_right_meas g₂) (s19r_mul_right_meas g₁), hc g₁, Measure.map_smul _ (s19r_mul_right_meas g₂).aemeasurable,
        hc g₂, smul_smul]
    refine hcancel _ _ ?_
    rw [← hev, e, Measure.smul_apply, smul_eq_mul]
  have hone : c 1 = 1 := hfix 1 (by
    rw [show (fun x : SL(2, ℝ) => x * 1) = id from funext mul_one, Measure.map_id])
  have hpos : ∀ g, c g ≠ 0 ∧ c g ≠ ∞ := by
    intro g
    have e : c g * c g⁻¹ = 1 := by rw [← hmul, mul_inv_cancel, hone]
    refine ⟨fun h0 => by rw [h0, zero_mul] at e; exact zero_ne_one e, fun ht => ?_⟩
    by_cases h0 : c g⁻¹ = 0
    · rw [h0, mul_zero] at e
      exact zero_ne_one e
    · rw [ht, ENNReal.top_mul h0] at e
      exact ENNReal.top_ne_one e
  have hrot : ∀ φ : ℝ, c (s19rIwasawa (UpperHalfPlane.I, φ)) = 1 := fun φ => hfix _ (s19r_rot_inv φ)
  have hcan2 : ∀ g x y, c g * x = c g * y → x = y := fun g x y hxy =>
    (ENNReal.mul_right_inj (hpos g).1 (hpos g).2).mp hxy
  -- `x ∈ (0, ∞)`, `x ^ k = x` (`k ≥ 2`) forces `x = 1`
  have hroot : ∀ x : ℝ≥0∞, x ≠ 0 → x ≠ ∞ → x * x = 1 ∨ x * x * x * x = x → x = 1 := by
    intro x h0 ht hx
    have hr : 0 < x.toReal := ENNReal.toReal_pos h0 ht
    rw [← ENNReal.ofReal_toReal ht]
    have : x.toReal = 1 := by
      rcases hx with hx | hx
      · have := congrArg ENNReal.toReal hx
        rw [ENNReal.toReal_mul, ENNReal.toReal_one] at this
        nlinarith
      · have := congrArg ENNReal.toReal hx
        rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul] at this
        have h3 : x.toReal * (x.toReal * x.toReal * x.toReal - 1) = 0 := by linear_combination this
        rcases mul_eq_zero.mp h3 with h | h
        · linarith
        · nlinarith [sq_nonneg (x.toReal - 1), sq_nonneg (x.toReal + 1)]
    rw [this, ENNReal.ofReal_one]
  -- explicit elements
  have hnex : ∀ x : ℝ, ∃ A : SL(2, ℝ), (A : Matrix (Fin 2) (Fin 2) ℝ) = !![1, x; 0, 1] := fun x =>
    ⟨⟨!![1, x; 0, 1], by simp [Matrix.det_fin_two]⟩, rfl⟩
  have haex : ∀ s : ℝ, ∃ A : SL(2, ℝ), 0 < s → (A : Matrix (Fin 2) (Fin 2) ℝ) = !![s, 0; 0, s⁻¹] := by
    intro s
    by_cases hs : 0 < s
    · exact ⟨⟨!![s, 0; 0, s⁻¹], by simp [Matrix.det_fin_two, hs.ne']⟩, fun _ => rfl⟩
    · exact ⟨1, fun h' => absurd h' hs⟩
  choose nx hnx using hnex
  choose as has using haex
  have hw : (s19rIwasawa (UpperHalfPlane.I, π / 2) : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -1; 1, 0] := by
    obtain ⟨e1, e2, e3, e4⟩ := s19r_iw_entries (UpperHalfPlane.I, π / 2)
    simp only [UpperHalfPlane.I_im, UpperHalfPlane.I_re, Real.sqrt_one, Real.cos_pi_div_two,
      Real.sin_pi_div_two, zero_div, div_one] at e1 e2 e3 e4
    ext i j
    fin_cases i <;> fin_cases j
    · simpa using e1
    · simpa using e2
    · simpa using e3
    · simpa using e4
  have hext : ∀ A B : SL(2, ℝ), (A : Matrix (Fin 2) (Fin 2) ℝ) = (B : Matrix (Fin 2) (Fin 2) ℝ) → A = B :=
    fun A B hAB => Subtype.ext hAB
  -- unipotents
  have hn : ∀ x : ℝ, c (nx x) = 1 := by
    intro x
    have h2 : (0 : ℝ) < 2 := by norm_num
    have e1 : as 2 * nx x = nx (4 * x) * as 2 := hext _ _ (by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, has 2 h2, hnx, hnx]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring)
    have e2 : nx x * nx x * nx x * nx x = nx (4 * x) := hext _ _ (by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.coe_mul, hnx, hnx]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring)
    have h1 : c (nx (4 * x)) = c (nx x) := by
      have := congrArg c e1
      rw [hmul, hmul, mul_comm (c (nx (4 * x)))] at this
      exact (hcan2 _ _ _ this).symm
    refine hroot _ (hpos _).1 (hpos _).2 (Or.inr ?_)
    rw [show c (nx x) * c (nx x) * c (nx x) * c (nx x) = c (nx x * nx x * nx x * nx x) by
      rw [hmul, hmul, hmul], e2, h1]
  -- diagonals
  have ha : ∀ s : ℝ, 0 < s → c (as s) = 1 := by
    intro s hs
    have hs' : 0 < s⁻¹ := inv_pos.mpr hs
    have e1 : s19rIwasawa (UpperHalfPlane.I, π / 2) * as s = as s⁻¹ * s19rIwasawa (UpperHalfPlane.I, π / 2) :=
      hext _ _ (by
        rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hw, has s hs, has s⁻¹ hs']
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two])
    have e2 : as s * as s⁻¹ = 1 := hext _ _ (by
      rw [Matrix.SpecialLinearGroup.coe_mul, has s hs, has s⁻¹ hs', Matrix.SpecialLinearGroup.coe_one]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hs.ne'])
    have h1 : c (as s⁻¹) = c (as s) := by
      have := congrArg c e1
      rw [hmul, hmul, hrot, one_mul, mul_one] at this
      exact this.symm
    refine hroot _ (hpos _).1 (hpos _).2 (Or.inl ?_)
    have := congrArg c e2
    rw [hmul, hone, h1] at this
    exact this
  -- `h = n_x a_{√y} k_θ`
  have hdec := s19r_iw_right h
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = (if arg ((h 1 1 : ℂ) + (h 1 0 : ℂ) * I) < 0 then
      arg ((h 1 1 : ℂ) + (h 1 0 : ℂ) * I) + 2 * π else arg ((h 1 1 : ℂ) + (h 1 0 : ℂ) * I)) := ⟨_, rfl⟩
  rw [← hθ] at hdec
  obtain ⟨τ, hτ⟩ : ∃ τ : ℍ, τ = (h • UpperHalfPlane.I : ℍ) := ⟨_, rfl⟩
  rw [← hτ] at hdec
  have hy : 0 < √τ.im := Real.sqrt_pos.mpr τ.im_pos
  have e3 : s19rIwasawa (τ, 0) = nx τ.re * as (√τ.im) := hext _ _ (by
    obtain ⟨e1, e2, e3, e4⟩ := s19r_iw_entries (τ, 0)
    simp only [Real.cos_zero, Real.sin_zero, mul_one, mul_zero, add_zero, neg_zero, zero_add] at e1 e2 e3 e4
    rw [Matrix.SpecialLinearGroup.coe_mul, hnx, has _ hy]
    ext i j
    fin_cases i <;> fin_cases j
    · simpa [Matrix.mul_apply, Fin.sum_univ_two] using e1
    · simpa [Matrix.mul_apply, Fin.sum_univ_two, div_eq_mul_inv] using e2
    · simpa [Matrix.mul_apply, Fin.sum_univ_two] using e3
    · simpa [Matrix.mul_apply, Fin.sum_univ_two] using e4)
  have hh : h = nx τ.re * as (√τ.im) * s19rIwasawa (UpperHalfPlane.I, θ) := by
    rw [← e3, s19r_iw_mul_rot, zero_add, hdec]
  have hch : c h = 1 := by rw [hh, hmul, hmul, hn, ha _ hy, hrot, one_mul, one_mul]
  rw [hc h, hch, one_smul]

/-- **R1b.** `s19rMeasure` is a bi-invariant σ-finite measure whose orbit map `g ↦ g • i` pushes it to `2π` times the
hyperbolic area. -/
theorem s19r_haar :
    (∀ h : SL(2, ℝ), Measure.map (h * ·) s19rMeasure = s19rMeasure) ∧
      (∀ h : SL(2, ℝ), Measure.map (· * h) s19rMeasure = s19rMeasure) ∧ SigmaFinite s19rMeasure ∧
      ∀ φ : ℍ → ℝ≥0∞, Measurable φ →
        ∫⁻ g, φ (g • UpperHalfPlane.I) ∂s19rMeasure = ENNReal.ofReal (2 * π) * ∫⁻ τ, φ τ := by
  exact ⟨s19r_left_inv, s19r_right_inv, s19r_sigma, fun φ hφ => s19r_orbit hφ⟩

/-- The Cayley coordinate `g ↦ C(g • i)` is measurable. -/
theorem s19r_cay_meas : Measurable fun g : SL(2, ℝ) =>
    (((g • UpperHalfPlane.I : ℍ) : ℂ) + I) / (((g • UpperHalfPlane.I : ℍ) : ℂ) - I) := by
  have hc : Measurable fun z : ℂ => (z + I) / (z - I) := by fun_prop
  exact hc.comp (UpperHalfPlane.measurable_coe.comp s19r_smul_meas)

/-- `s19rDomain Γ` is measurable. -/
theorem s19r_dom_meas (Γ : Subgroup SL2C) : MeasurableSet (s19rDomain Γ) := by
  have hA : MeasurableSet {g : SL(2, ℝ) | 0 < g 1 0 ∨ (g 1 0 = 0 ∧ 0 < g 1 1)} :=
    (measurableSet_lt measurable_const (s19r_meas_entry 1 0)).union
      ((measurableSet_eq_fun (s19r_meas_entry 1 0) measurable_const).inter
        (measurableSet_lt measurable_const (s19r_meas_entry 1 1)))
  exact (s19r_cay_meas (fundDomain_measurable Γ)).inter hA

/-- A Lebesgue-null set of `ℂ` has `μ`-null preimage under the orbit map `g ↦ g • i`. -/
theorem s19r_null {P : Set ℂ} (hP : volume P = 0) :
    s19rMeasure {g : SL(2, ℝ) | ((g • UpperHalfPlane.I : ℍ) : ℂ) ∈ P} = 0 := by
  have hm : Measurable fun g : SL(2, ℝ) => ((g • UpperHalfPlane.I : ℍ) : ℂ) :=
    UpperHalfPlane.measurable_coe.comp s19r_smul_meas
  obtain ⟨T, hT⟩ : ∃ T, T = toMeasurable volume P := ⟨_, rfl⟩
  have hTm : MeasurableSet T := by rw [hT]; exact measurableSet_toMeasurable _ _
  have hT0 : volume T = 0 := by rw [hT, measure_toMeasurable]; exact hP
  have hPT : P ⊆ T := by rw [hT]; exact subset_toMeasurable _ _
  refine measure_mono_null (t := (fun g : SL(2, ℝ) => ((g • UpperHalfPlane.I : ℍ) : ℂ)) ⁻¹' T)
    (fun g hg => hPT hg) ?_
  have hQm : MeasurableSet (((↑) : ℍ → ℂ) ⁻¹' T) := UpperHalfPlane.measurable_coe hTm
  have h := s19r_orbit (φ := (((↑) : ℍ → ℂ) ⁻¹' T).indicator 1) (measurable_one.indicator hQm)
  have e : (fun g : SL(2, ℝ) => ((((↑) : ℍ → ℂ) ⁻¹' T).indicator (1 : ℍ → ℝ≥0∞)) (g • UpperHalfPlane.I)) =
      ((fun g : SL(2, ℝ) => ((g • UpperHalfPlane.I : ℍ) : ℂ)) ⁻¹' T).indicator 1 := by
    funext g
    by_cases hg : ((g • UpperHalfPlane.I : ℍ) : ℂ) ∈ T
    · rw [indicator_of_mem (show (g • UpperHalfPlane.I : ℍ) ∈ ((↑) : ℍ → ℂ) ⁻¹' T from hg),
        indicator_of_mem (show g ∈ (fun g : SL(2, ℝ) => ((g • UpperHalfPlane.I : ℍ) : ℂ)) ⁻¹' T from hg)]
      rfl
    · rw [indicator_of_notMem (show (g • UpperHalfPlane.I : ℍ) ∉ ((↑) : ℍ → ℂ) ⁻¹' T from hg),
        indicator_of_notMem (show g ∉ (fun g : SL(2, ℝ) => ((g • UpperHalfPlane.I : ℍ) : ℂ)) ⁻¹' T from hg)]
  rw [e, lintegral_indicator_one (hm hTm), lintegral_indicator_one hQm,
    UpperHalfPlane.volume_eq_lintegral,
    setLIntegral_measure_zero _ _ (measure_mono_null (image_preimage_subset _ _) hT0), mul_zero] at h
  exact h

/-- The Cayley pull-back of a null set, inside the lifted fundamental domain, is null. -/
theorem s19r_cay_null {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {Γ' : Subgroup SL(2, ℝ)}
    (hrel : ∀ M ∈ Γ', ∃ g ∈ Γ, ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I))
    (hrel' : ∀ g ∈ Γ, ∃ M ∈ Γ', ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I))
    {Z : Set ℂ} (hZ : volume Z = 0) :
    volume {z : ℂ | 0 < z.im ∧ (z + I) / (z - I) ∈ fundDomain Γ ∧ (z + I) / (z - I) ∈ Z} = 0 := by
  obtain ⟨hF'm, -, -, htr⟩ := s13c_transfer_cover hΓ hrel hrel'
  obtain ⟨T, hT⟩ : ∃ T, T = toMeasurable volume Z := ⟨_, rfl⟩
  have hTm : MeasurableSet T := by rw [hT]; exact measurableSet_toMeasurable _ _
  have hT0 : volume T = 0 := by rw [hT, measure_toMeasurable]; exact hZ
  have hZT : Z ⊆ T := by rw [hT]; exact subset_toMeasurable _ _
  have hcm : Measurable fun z : ℂ => (z + I) / (z - I) := by fun_prop
  have hR : ∫⁻ w in fundDomain Γ, T.indicator 1 w * ENNReal.ofReal (rho w) = 0 := by
    calc ∫⁻ w in fundDomain Γ, T.indicator 1 w * ENNReal.ofReal (rho w)
        = ∫⁻ _ in fundDomain Γ, (0 : ℝ≥0∞) := by
          refine lintegral_congr_ae (ae_restrict_of_ae ?_)
          filter_upwards [measure_eq_zero_iff_ae_notMem.mp hT0] with w hw
          rw [indicator_of_notMem hw, zero_mul]
      _ = 0 := lintegral_zero
  have h := htr (T.indicator 1) (measurable_one.indicator hTm)
  rw [hR] at h
  have hfm : Measurable fun z : ℂ => T.indicator (1 : ℂ → ℝ≥0∞) ((z + I) / (z - I)) * ENNReal.ofReal ((z.im ^ 2)⁻¹) :=
    ((measurable_one.indicator hTm).comp hcm).mul (ENNReal.measurable_ofReal.comp (by fun_prop))
  have h0 := (lintegral_eq_zero_iff hfm).mp h
  rw [Filter.EventuallyEq, ae_restrict_iff' hF'm] at h0
  refine measure_mono_null ?_ (ae_iff.mp h0)
  intro z hz hP
  have hv := hP ⟨hz.1, hz.2.1⟩
  rw [Pi.zero_apply, indicator_of_mem (hZT hz.2.2), Pi.one_apply, one_mul, ENNReal.ofReal_eq_zero] at hv
  have : 0 < (z.im ^ 2)⁻¹ := inv_pos.mpr (pow_pos hz.1 2)
  linarith

/-- In Iwasawa coordinates (`θ ∈ [0, 2π)`), the second-row condition of `s19rDomain` is `θ < π`. -/
theorem s19r_angle (τ : ℍ) {θ : ℝ} (hθ : θ ∈ Ico (0 : ℝ) (2 * π)) :
    (0 < s19rIwasawa (τ, θ) 1 0 ∨ (s19rIwasawa (τ, θ) 1 0 = 0 ∧ 0 < s19rIwasawa (τ, θ) 1 1)) ↔ θ < π := by
  obtain ⟨-, -, e3, e4⟩ := s19r_iw_entries (τ, θ)
  dsimp only at e3 e4
  have hy : 0 < 1 / √τ.im := one_div_pos.mpr (Real.sqrt_pos.mpr τ.im_pos)
  rw [e3, e4]
  have hs : π ≤ θ → Real.sin θ ≤ 0 := fun h => by
    have := Real.sin_nonneg_of_nonneg_of_le_pi (x := θ - π) (by linarith) (by linarith [hθ.2])
    rw [Real.sin_sub_pi] at this
    linarith
  constructor
  · rintro (h | ⟨h1, h2⟩)
    · by_contra hc
      have := mul_nonpos_of_nonneg_of_nonpos hy.le (hs (not_lt.mp hc))
      linarith
    · by_contra hc
      have hsin : Real.sin θ = 0 := by
        rcases mul_eq_zero.mp h1 with h | h
        · exact absurd h hy.ne'
        · exact h
      have hcos : 0 < Real.cos θ := (mul_pos_iff_of_pos_left hy).mp h2
      have hπθ : θ = π := by
        by_contra hne
        have hlt : π < θ := lt_of_le_of_ne (not_lt.mp hc) (Ne.symm hne)
        have := Real.sin_pos_of_pos_of_lt_pi (x := θ - π) (by linarith) (by linarith [hθ.2])
        rw [Real.sin_sub_pi, hsin] at this
        linarith
      rw [hπθ, Real.cos_pi] at hcos
      linarith
  · intro hlt
    rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · right
      rw [← h0, Real.sin_zero, Real.cos_zero, mul_zero, mul_one]
      exact ⟨rfl, hy⟩
    · left
      exact mul_pos hy (Real.sin_pos_of_pos_of_lt_pi h0 hlt)

/-- `mob 1 = id`. -/
theorem s19r_mob_one (z : ℂ) : mob 1 z = z := by
  simp [mob]

/-- `(-1) X = -X` in `SL(2, ℝ)`. -/
theorem s19r_neg_one_mul (X : SL(2, ℝ)) : (-1 : SL(2, ℝ)) * X = -X :=
  Matrix.SpecialLinearGroup.ext _ _ fun i j => by simp

/-- Exactly one of `X`, `-X` satisfies the second-row condition of `s19rDomain`. -/
theorem s19r_sign (X : SL(2, ℝ)) :
    ((0 < X 1 0 ∨ (X 1 0 = 0 ∧ 0 < X 1 1)) ∨ (0 < (-X) 1 0 ∨ ((-X) 1 0 = 0 ∧ 0 < (-X) 1 1))) ∧
      ¬((0 < X 1 0 ∨ (X 1 0 = 0 ∧ 0 < X 1 1)) ∧ (0 < (-X) 1 0 ∨ ((-X) 1 0 = 0 ∧ 0 < (-X) 1 1))) := by
  have hd : X 0 0 * X 1 1 - X 0 1 * X 1 0 = 1 := by
    have h := X.2
    rw [Matrix.det_fin_two] at h
    exact h
  have e0 : (-X) 1 0 = -X 1 0 := by simp [Matrix.SpecialLinearGroup.coe_neg]
  have e1 : (-X) 1 1 = -X 1 1 := by simp [Matrix.SpecialLinearGroup.coe_neg]
  rw [e0, e1]
  constructor
  · rcases lt_trichotomy (X 1 0) 0 with h | h | h
    · exact Or.inr (Or.inl (by linarith))
    · rcases lt_trichotomy (X 1 1) 0 with h' | h' | h'
      · exact Or.inr (Or.inr ⟨by rw [h, neg_zero], by linarith⟩)
      · rw [h, h', mul_zero, mul_zero, sub_zero] at hd
        exact absurd hd zero_ne_one
      · exact Or.inl (Or.inr ⟨h, h'⟩)
    · exact Or.inl (Or.inl h)
  · rintro ⟨h1 | ⟨h1, h2⟩, h3 | ⟨h3, h4⟩⟩
    · linarith
    · linarith
    · linarith
    · linarith

/-- `Γ'`-translates of `s19rDomain Γ` cover `SL(2, ℝ)` a.e. -/
theorem s19r_cover {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {Γ' : Subgroup SL(2, ℝ)} (hneg : -1 ∈ Γ')
    (hrel : ∀ M ∈ Γ', ∃ g ∈ Γ, ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I))
    (hrel' : ∀ g ∈ Γ, ∃ M ∈ Γ', ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I)) :
    ∀ᵐ g ∂s19rMeasure, ∃ γ : Γ', γ • g ∈ s19rDomain Γ := by
  obtain ⟨-, -, hcov, -⟩ := s13c_transfer_cover hΓ hrel hrel'
  have hU : MeasurableSet upperHalf := measurableSet_lt measurable_const Complex.measurable_im
  rw [ae_restrict_iff' hU] at hcov
  rw [ae_iff]
  refine measure_mono_null ?_ (s19r_null (ae_iff.mp hcov))
  intro g hg hP
  apply hg
  have hz : 0 < ((g • UpperHalfPlane.I : ℍ) : ℂ).im := (g • UpperHalfPlane.I).im_pos
  obtain ⟨M, hM, hMF⟩ := hP hz hz
  have hMF' : (((M * g) • UpperHalfPlane.I : ℍ) : ℂ) ∈
      {z : ℂ | 0 < z.im ∧ (z + I) / (z - I) ∈ fundDomain Γ} := by
    rw [mul_smul]
    exact hMF
  rcases (s19r_sign (M * g)).1 with hA | hA
  · refine ⟨⟨M, hM⟩, ?_⟩
    show ((((M * g) • UpperHalfPlane.I : ℍ) : ℂ) + I) / ((((M * g) • UpperHalfPlane.I : ℍ) : ℂ) - I) ∈
      fundDomain Γ ∧ (0 < (M * g) 1 0 ∨ ((M * g) 1 0 = 0 ∧ 0 < (M * g) 1 1))
    exact ⟨hMF'.2, hA⟩
  · refine ⟨⟨-1 * M, Subgroup.mul_mem _ hneg hM⟩, ?_, ?_⟩
    · show ((((-1 * M * g) • UpperHalfPlane.I : ℍ) : ℂ) + I) /
          ((((-1 * M * g) • UpperHalfPlane.I : ℍ) : ℂ) - I) ∈ fundDomain Γ
      rw [mul_assoc, s19r_neg_one_mul, s13c_neg_smul]
      exact hMF'.2
    · show 0 < (-1 * M * g) 1 0 ∨ ((-1 * M * g) 1 0 = 0 ∧ 0 < (-1 * M * g) 1 1)
      rw [mul_assoc, s19r_neg_one_mul]
      exact hA

/-- `s19rDomain Γ ∩ M⁻¹ s19rDomain Γ` is null for `1 ≠ M ∈ Γ'`. -/
theorem s19r_disj {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {Γ' : Subgroup SL(2, ℝ)}
    (hrel : ∀ M ∈ Γ', ∃ g ∈ Γ, ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I))
    (hrel' : ∀ g ∈ Γ, ∃ M ∈ Γ', ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I))
    {M : SL(2, ℝ)} (hM : M ∈ Γ') (hM1 : M ≠ 1) :
    s19rMeasure {x | x ∈ s19rDomain Γ ∧ M * x ∈ s19rDomain Γ} = 0 := by
  obtain ⟨g, hg, hgM⟩ := hrel M hM
  have hfd := isFundDomain_fundDomain hΓ.1
  by_cases hid : mob g = mob 1
  · -- `M` acts trivially through the Cayley map, so `M = ±1`, and `-1` flips the second-row condition
    have hfix : ∀ τ : ℍ, (τ : ℂ) ≠ I → ((M • τ : ℍ) : ℂ) ≠ I → M • τ = τ := by
      intro τ h1 h2
      have e := hgM τ h1 h2
      rw [hid, s19r_mob_one] at e
      apply UpperHalfPlane.ext
      calc ((M • τ : ℍ) : ℂ)
          = I * ((((M • τ : ℍ) : ℂ) + I) / (((M • τ : ℍ) : ℂ) - I) + 1) /
              ((((M • τ : ℍ) : ℂ) + I) / (((M • τ : ℍ) : ℂ) - I) - 1) :=
            (s13c_cayInv_cay (sub_ne_zero.mpr h2)).symm
        _ = I * (((τ : ℂ) + I) / ((τ : ℂ) - I) + 1) / (((τ : ℂ) + I) / ((τ : ℂ) - I) - 1) := by rw [e]
        _ = τ := s13c_cayInv_cay (sub_ne_zero.mpr h1)
    have hpt : ∀ t : ℝ, 1 < t → ∃ τ : ℍ, (τ : ℂ) = (t : ℂ) * I := fun t ht =>
      ⟨⟨(t : ℂ) * I, by simp; linarith⟩, rfl⟩
    obtain ⟨τ2, h2⟩ := hpt 2 (by norm_num)
    obtain ⟨τ3, h3⟩ := hpt 3 (by norm_num)
    obtain ⟨τ4, h4⟩ := hpt 4 (by norm_num)
    have hnI : ∀ τ : ℍ, ∀ t : ℝ, 1 < t → (τ : ℂ) = (t : ℂ) * I → (τ : ℂ) ≠ I := by
      intro τ t ht hτ h
      have := congrArg Complex.im (hτ.symm.trans h)
      simp at this
      linarith
    have hne : ∀ σ ρ : ℍ, ∀ s t : ℝ, s ≠ t → (σ : ℂ) = (s : ℂ) * I → (ρ : ℂ) = (t : ℂ) * I → σ ≠ ρ := by
      intro σ ρ s t hst hσ hρ h
      have := congrArg Complex.im (hσ.symm.trans ((congrArg UpperHalfPlane.coe h).trans hρ))
      simp at this
      exact hst this
    have hcan : ∀ σ ρ : ℍ, σ ≠ ρ → ((M • σ : ℍ) : ℂ) = I → ((M • ρ : ℍ) : ℂ) ≠ I := by
      intro σ ρ hσρ hσ hρ
      exact hσρ (smul_left_cancel M (UpperHalfPlane.ext (hσ.trans hρ.symm)))
    have h23 := hne τ2 τ3 2 3 (by norm_num) h2 h3
    have h24 := hne τ2 τ4 2 4 (by norm_num) h2 h4
    have h34 := hne τ3 τ4 3 4 (by norm_num) h3 h4
    have hpm : M = 1 ∨ M = -1 := by
      by_cases k2 : ((M • τ2 : ℍ) : ℂ) = I
      · exact s13c_fix_unique M (hfix τ3 (hnI τ3 3 (by norm_num) h3) (hcan τ2 τ3 h23 k2))
          (hfix τ4 (hnI τ4 4 (by norm_num) h4) (hcan τ2 τ4 h24 k2)) h34
      · by_cases k3 : ((M • τ3 : ℍ) : ℂ) = I
        · exact s13c_fix_unique M (hfix τ2 (hnI τ2 2 (by norm_num) h2) k2)
            (hfix τ4 (hnI τ4 4 (by norm_num) h4) (hcan τ3 τ4 h34 k3)) h24
        · exact s13c_fix_unique M (hfix τ2 (hnI τ2 2 (by norm_num) h2) k2)
            (hfix τ3 (hnI τ3 3 (by norm_num) h3) k3) h23
    rcases hpm with h1 | h1
    · exact absurd h1 hM1
    · refine measure_mono_null (t := ∅) ?_ measure_empty
      intro x hx
      have hx2 := hx.2.2
      rw [h1, s19r_neg_one_mul] at hx2
      exact (s19r_sign x).2 ⟨hx.1.2, hx2⟩
  · have hZ := hfd.2.2.2 g hg 1 (Subgroup.one_mem _) hid
    refine measure_mono_null (t := {x : SL(2, ℝ) | ((x • UpperHalfPlane.I : ℍ) : ℂ) ∈
        {z : ℂ | 0 < z.im ∧ (z + I) / (z - I) ∈ fundDomain Γ ∧
          (z + I) / (z - I) ∈ mob g ⁻¹' fundDomain Γ ∩ mob 1 ⁻¹' fundDomain Γ ∩ unitDiscExterior}} ∪
        {x : SL(2, ℝ) | ((x • UpperHalfPlane.I : ℍ) : ℂ) ∈ ({I} : Set ℂ)} ∪
        {x : SL(2, ℝ) | ((x • UpperHalfPlane.I : ℍ) : ℂ) ∈ ({((M⁻¹ • UpperHalfPlane.I : ℍ) : ℂ)} : Set ℂ)})
      ?_ (measure_union_null (measure_union_null (s19r_null (s19r_cay_null hΓ hrel hrel' hZ))
        (s19r_null (measure_singleton _))) (s19r_null (measure_singleton _)))
    intro x hx
    by_cases k1 : ((x • UpperHalfPlane.I : ℍ) : ℂ) = I
    · exact Or.inl (Or.inr k1)
    by_cases k2 : ((M • (x • UpperHalfPlane.I) : ℍ) : ℂ) = I
    · refine Or.inr ?_
      show ((x • UpperHalfPlane.I : ℍ) : ℂ) ∈ ({((M⁻¹ • UpperHalfPlane.I : ℍ) : ℂ)} : Set ℂ)
      rw [mem_singleton_iff]
      have hM' : M • (x • UpperHalfPlane.I) = UpperHalfPlane.I := UpperHalfPlane.ext k2
      exact congrArg UpperHalfPlane.coe (eq_inv_smul_iff.mpr hM')
    · refine Or.inl (Or.inl ⟨(x • UpperHalfPlane.I).im_pos, hx.1.1, ⟨⟨?_, ?_⟩, hfd.2.1 hx.1.1⟩⟩)
      · have e := hgM (x • UpperHalfPlane.I) k1 k2
        have hMx : ((((M • (x • UpperHalfPlane.I)) : ℍ) : ℂ) + I) /
            ((((M • (x • UpperHalfPlane.I)) : ℍ) : ℂ) - I) ∈ fundDomain Γ := by
          rw [← mul_smul]
          exact hx.2.1
        show mob g ((((x • UpperHalfPlane.I : ℍ) : ℂ) + I) / (((x • UpperHalfPlane.I : ℍ) : ℂ) - I)) ∈ fundDomain Γ
        rw [e]
        exact hMx
      · show mob 1 ((((x • UpperHalfPlane.I : ℍ) : ℂ) + I) / (((x • UpperHalfPlane.I : ℍ) : ℂ) - I)) ∈ fundDomain Γ
        rw [s19r_mob_one]
        exact hx.1.1

/-- `s19rDomain Γ` is a fundamental domain of left `Γ'`-multiplication. -/
theorem s19r_fd {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {Γ' : Subgroup SL(2, ℝ)} (hneg : -1 ∈ Γ')
    (hrel : ∀ M ∈ Γ', ∃ g ∈ Γ, ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I))
    (hrel' : ∀ g ∈ Γ, ∃ M ∈ Γ', ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I)) :
    IsFundamentalDomain Γ' (s19rDomain Γ) s19rMeasure := by
  refine IsFundamentalDomain.mk'' (s19r_dom_meas Γ).nullMeasurableSet (s19r_cover hΓ hneg hrel hrel') ?_ ?_
  · intro γ hγ
    refine measure_mono_null ?_ (s19r_disj hΓ hrel hrel' (γ⁻¹ : Γ').2 fun h => hγ (inv_eq_one.mp (Subtype.ext h)))
    intro x hx
    exact ⟨hx.2, mem_smul_set_iff_inv_smul_mem.mp hx.1⟩
  · intro γ
    exact (MeasurePreserving.mk (s19r_mul_left_meas γ) (s19r_left_inv γ)).quasiMeasurePreserving

/-- Right translates of `s19rDomain Γ` are fundamental domains as well. -/
theorem s19r_fd_right {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {Γ' : Subgroup SL(2, ℝ)} (hneg : -1 ∈ Γ')
    (hrel : ∀ M ∈ Γ', ∃ g ∈ Γ, ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I))
    (hrel' : ∀ g ∈ Γ, ∃ M ∈ Γ', ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I))
    (h : SL(2, ℝ)) : IsFundamentalDomain Γ' ((· * h) '' s19rDomain Γ) s19rMeasure := by
  have hq : Measure.QuasiMeasurePreserving (Equiv.mulRight h).symm s19rMeasure s19rMeasure := by
    rw [Equiv.mulRight_symm, Equiv.coe_mulRight]
    exact (MeasurePreserving.mk (s19r_mul_right_meas h⁻¹) (s19r_right_inv h⁻¹)).quasiMeasurePreserving
  have := (s19r_fd hΓ hneg hrel hrel').image_of_equiv (Equiv.mulRight h) hq (Equiv.refl _)
    (fun γ x => by
      show ((γ : SL(2, ℝ)) * x) * h = (γ : SL(2, ℝ)) * (x * h)
      exact mul_assoc _ _ _)
  rwa [Equiv.coe_mulRight] at this

/-- For a.e. `g ∈ s19rDomain Γ` exactly one `γ ∈ Γ'` folds `g h` back into the domain. -/
theorem s19r_unique {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {Γ' : Subgroup SL(2, ℝ)} (hΓ' : LiZhongQC.IsFuchsian Γ')
    (hneg : -1 ∈ Γ')
    (hrel : ∀ M ∈ Γ', ∃ g ∈ Γ, ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I))
    (hrel' : ∀ g ∈ Γ, ∃ M ∈ Γ', ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I))
    (h : SL(2, ℝ)) :
    ∀ᵐ g ∂(s19rMeasure.restrict (s19rDomain Γ)), ∃! γ : Γ', (γ : SL(2, ℝ)) * g * h ∈ s19rDomain Γ := by
  haveI := s13c_countable hΓ'
  have hfd := s19r_fd hΓ hneg hrel hrel'
  have hu : ∀ᵐ x ∂s19rMeasure, ∀ γ₁ γ₂ : Γ', (γ₁ : SL(2, ℝ)) * x ∈ s19rDomain Γ →
      (γ₂ : SL(2, ℝ)) * x ∈ s19rDomain Γ → γ₁ = γ₂ := by
    rw [ae_all_iff]
    intro γ₁
    rw [ae_all_iff]
    intro γ₂
    by_cases e : γ₁ = γ₂
    · exact Eventually.of_forall fun _ _ _ => e
    · have hd :=
        hfd.aedisjoint (show γ₁⁻¹ ≠ γ₂⁻¹ from fun h' => e (inv_injective h'))
      rw [ae_iff]
      refine measure_mono_null ?_ hd
      intro x hx
      simp only [Set.mem_ofPred_eq, not_imp] at hx
      refine ⟨mem_smul_set_iff_inv_smul_mem.mpr ?_, mem_smul_set_iff_inv_smul_mem.mpr ?_⟩
      · rw [inv_inv]
        exact hx.1
      · rw [inv_inv]
        exact hx.2.1
  have hmp : MeasurePreserving (· * h) s19rMeasure s19rMeasure := ⟨s19r_mul_right_meas h, s19r_right_inv h⟩
  have hall := hmp.quasiMeasurePreserving.ae (hfd.ae_covers.and hu)
  refine ae_restrict_of_ae ?_
  filter_upwards [hall] with g hg
  obtain ⟨⟨γ, hγ⟩, hu'⟩ := hg
  refine ⟨γ, ?_, fun γ' hγ' => hu' γ' γ ?_ hγ⟩
  · show (γ : SL(2, ℝ)) * g * h ∈ s19rDomain Γ
    rw [mul_assoc]
    exact hγ
  · show (γ' : SL(2, ℝ)) * (g * h) ∈ s19rDomain Γ
    rw [← mul_assoc]
    exact hγ'

/-- Integrals over `ℍ` against Mathlib's hyperbolic area, as integrals over the upper half-plane of `ℂ`. -/
theorem s19r_hyp_lint {G : ℂ → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ τ : ℍ, G τ = ∫⁻ z in upperHalf, G z * ENNReal.ofReal ((z.im ^ 2)⁻¹) := by
  have hw : (fun z : ℍ => (((1 / NNReal.mk z.im z.im_pos.le : NNReal) ^ 2 : NNReal) : ℝ≥0∞)) =
      fun z : ℍ => ENNReal.ofReal (((z : ℂ).im ^ 2)⁻¹) := by
    funext z
    rw [← ENNReal.ofReal_coe_nnreal]
    congr 1
    simp [one_div, inv_pow]
  have hwm : Measurable fun z : ℍ => ENNReal.ofReal (((z : ℂ).im ^ 2)⁻¹) :=
    ENNReal.measurable_ofReal.comp
      ((by fun_prop : Measurable fun z : ℂ => (z.im ^ 2)⁻¹).comp UpperHalfPlane.measurable_coe)
  have hmp : MeasurePreserving UpperHalfPlane.coe (volume.comap UpperHalfPlane.coe)
      (volume.restrict (range UpperHalfPlane.coe)) :=
    ⟨UpperHalfPlane.measurable_coe, by rw [UpperHalfPlane.measurableEmbedding_coe.map_comap]⟩
  have hr : range UpperHalfPlane.coe = upperHalf := by
    ext z
    exact ⟨by rintro ⟨τ, rfl⟩; exact τ.im_pos, fun h => ⟨⟨z, h⟩, rfl⟩⟩
  rw [UpperHalfPlane.volume_def, hw,
    lintegral_withDensity_eq_lintegral_mul _ hwm (g := fun τ : ℍ => G τ) (hG.comp UpperHalfPlane.measurable_coe), ← hr,
    ← hmp.lintegral_comp_emb UpperHalfPlane.measurableEmbedding_coe]
  refine lintegral_congr fun τ => ?_
  simp only [Pi.mul_apply, Function.comp_apply]
  exact mul_comm _ _

/-- **Unfolding over `s19rDomain`**: `∫_D φ(C(g • i)) dμ = π ∫_F φ ρ`. -/
theorem s19r_dom_int {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {Γ' : Subgroup SL(2, ℝ)}
    (hrel : ∀ M ∈ Γ', ∃ g ∈ Γ, ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I))
    (hrel' : ∀ g ∈ Γ, ∃ M ∈ Γ', ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I))
    {φ : ℂ → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ g in s19rDomain Γ,
        φ ((((g • UpperHalfPlane.I : ℍ) : ℂ) + I) / (((g • UpperHalfPlane.I : ℍ) : ℂ) - I)) ∂s19rMeasure =
      ENNReal.ofReal π * ∫⁻ w in fundDomain Γ, φ w * ENNReal.ofReal (rho w) := by
  have hπ := Real.pi_pos
  obtain ⟨hF'm, hF'H, -, htr⟩ := s13c_transfer_cover hΓ hrel hrel'
  have hcm : Measurable fun z : ℂ => (z + I) / (z - I) := by fun_prop
  obtain ⟨G, hG⟩ : ∃ G : ℂ → ℝ≥0∞, G = {z : ℂ | 0 < z.im ∧ (z + I) / (z - I) ∈ fundDomain Γ}.indicator
      (fun z => φ ((z + I) / (z - I))) := ⟨_, rfl⟩
  have hGm : Measurable G := by rw [hG]; exact (hφ.comp hcm).indicator hF'm
  have hf : Measurable fun g : SL(2, ℝ) =>
      φ ((((g • UpperHalfPlane.I : ℍ) : ℂ) + I) / (((g • UpperHalfPlane.I : ℍ) : ℂ) - I)) :=
    hφ.comp s19r_cay_meas
  have hDm := s19r_dom_meas Γ
  have hset : Iio π ∩ Ico (0 : ℝ) (2 * π) = Ico 0 π := by
    ext θ
    simp only [mem_inter_iff, mem_Iio, mem_Ico]
    constructor
    · rintro ⟨h1, h2, -⟩
      exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h2, h1, by linarith⟩
  have hin : ∀ τ : ℍ, ∫⁻ θ in Ico (0 : ℝ) (2 * π), (s19rDomain Γ).indicator (fun g : SL(2, ℝ) =>
      φ ((((g • UpperHalfPlane.I : ℍ) : ℂ) + I) / (((g • UpperHalfPlane.I : ℍ) : ℂ) - I))) (s19rIwasawa (τ, θ)) =
        G τ * ENNReal.ofReal π := by
    intro τ
    rw [setLIntegral_congr_fun measurableSet_Ico (g := (Iio π).indicator fun _ => G τ) ?_]
    · rw [lintegral_indicator_const measurableSet_Iio, Measure.restrict_apply measurableSet_Iio, hset,
        Real.volume_Ico, sub_zero]
    · intro θ hθ
      beta_reduce
      by_cases hθπ : θ < π
      · rw [indicator_of_mem (show θ ∈ Iio π from hθπ)]
        by_cases hτ : ((τ : ℂ) + I) / ((τ : ℂ) - I) ∈ fundDomain Γ
        · have hmem : s19rIwasawa (τ, θ) ∈ s19rDomain Γ :=
            ⟨by rw [s19r_iw_smul]; exact hτ, (s19r_angle τ hθ).mpr hθπ⟩
          rw [indicator_of_mem hmem, hG,
            indicator_of_mem (show (τ : ℂ) ∈ {z : ℂ | 0 < z.im ∧ (z + I) / (z - I) ∈ fundDomain Γ} from
              ⟨τ.im_pos, hτ⟩), s19r_iw_smul]
        · have hnm : s19rIwasawa (τ, θ) ∉ s19rDomain Γ := fun h => hτ (by
            have h1 := h.1
            rwa [s19r_iw_smul] at h1)
          rw [indicator_of_notMem hnm, hG, indicator_of_notMem (show (τ : ℂ) ∉
            {z : ℂ | 0 < z.im ∧ (z + I) / (z - I) ∈ fundDomain Γ} from fun h => hτ h.2)]
      · rw [indicator_of_notMem (show θ ∉ Iio π from hθπ),
          indicator_of_notMem (fun h : s19rIwasawa (τ, θ) ∈ s19rDomain Γ => hθπ ((s19r_angle τ hθ).mp h.2))]
  rw [← lintegral_indicator hDm]
  show ∫⁻ g, (s19rDomain Γ).indicator (fun g : SL(2, ℝ) =>
      φ ((((g • UpperHalfPlane.I : ℍ) : ℂ) + I) / (((g • UpperHalfPlane.I : ℍ) : ℂ) - I))) g
        ∂(Measure.map s19rIwasawa ((volume : Measure ℍ).prod (volume.restrict (Ico 0 (2 * π))))) = _
  rw [lintegral_map (hf.indicator hDm) s19r_iw_meas,
    lintegral_prod (fun p : ℍ × ℝ => (s19rDomain Γ).indicator (fun g : SL(2, ℝ) =>
      φ ((((g • UpperHalfPlane.I : ℍ) : ℂ) + I) / (((g • UpperHalfPlane.I : ℍ) : ℂ) - I))) (s19rIwasawa p))
      ((hf.indicator hDm).comp s19r_iw_meas).aemeasurable]
  refine (lintegral_congr hin).trans ?_
  rw [lintegral_mul_const (f := fun τ : ℍ => G τ) _ (hGm.comp UpperHalfPlane.measurable_coe), s19r_hyp_lint hGm,
    mul_comm]
  congr 1
  have hU : MeasurableSet upperHalf := measurableSet_lt measurable_const Complex.measurable_im
  rw [← htr φ hφ, ← lintegral_indicator hU, ← lintegral_indicator hF'm]
  refine lintegral_congr fun z => ?_
  by_cases hz : z ∈ {z : ℂ | 0 < z.im ∧ (z + I) / (z - I) ∈ fundDomain Γ}
  · rw [indicator_of_mem (hF'H hz), indicator_of_mem hz, hG, indicator_of_mem hz]
  · rw [indicator_of_notMem hz, hG]
    by_cases hu : z ∈ upperHalf
    · rw [indicator_of_mem hu, indicator_of_notMem hz, zero_mul]
    · rw [indicator_of_notMem hu]

/-- **R2.** `s19rDomain Γ` is a measurable fundamental domain of left `Γ'`-multiplication, so are its right translates
(for a.e. `g ∈ D` exactly one `γ` folds `g h` back into `D`), and integrals of lifts over it are `π` times integrals over `F` against `ρ`. -/
theorem s19r_domain {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {Γ' : Subgroup SL(2, ℝ)} (hΓ' : LiZhongQC.IsFuchsian Γ') (hneg : -1 ∈ Γ')
    (hrel : ∀ M ∈ Γ', ∃ g ∈ Γ, ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I))
    (hrel' : ∀ g ∈ Γ, ∃ M ∈ Γ', ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I)) :
    MeasurableSet (s19rDomain Γ) ∧
      (∀ h : SL(2, ℝ), IsFundamentalDomain Γ' ((· * h) '' s19rDomain Γ) s19rMeasure) ∧
      (∀ h : SL(2, ℝ), ∀ᵐ g ∂(s19rMeasure.restrict (s19rDomain Γ)),
        ∃! γ : Γ', (γ : SL(2, ℝ)) * g * h ∈ s19rDomain Γ) ∧
      ∀ φ : ℂ → ℝ≥0∞, Measurable φ →
        ∫⁻ g in s19rDomain Γ,
            φ ((((g • UpperHalfPlane.I : ℍ) : ℂ) + I) / (((g • UpperHalfPlane.I : ℍ) : ℂ) - I)) ∂s19rMeasure =
          ENNReal.ofReal π * ∫⁻ w in fundDomain Γ, φ w * ENNReal.ofReal (rho w) := by
  exact ⟨s19r_dom_meas Γ, fun h => s19r_fd_right hΓ hneg hrel hrel' h,
    fun h => s19r_unique hΓ hΓ' hneg hrel hrel' h, fun φ hφ => s19r_dom_int hΓ hrel hrel' hφ⟩

/-- A `Γ'`-series of `1_D F` with at most one index `γ₀` landing in `D`. -/
theorem s19r_tsum_single {Γ : Subgroup SL2C} {Γ' : Subgroup SL(2, ℝ)} (F : SL(2, ℝ) → ℝ) (k : Γ' → SL(2, ℝ))
    (γ₀ : Γ') (hk : ∀ γ : Γ', k γ ∈ s19rDomain Γ → γ = γ₀) :
    ∑' γ : Γ', (s19rDomain Γ).indicator F (k γ) = (s19rDomain Γ).indicator F (k γ₀) :=
  tsum_eq_single γ₀ fun γ hγ => indicator_of_notMem (fun hm => hγ (hk γ hm)) _

/-- Left `Γ'`-periodicity of a `Γ'`-series. -/
theorem s19r_per_inv {Γ' : Subgroup SL(2, ℝ)} (F : SL(2, ℝ) → ℝ) (γ₁ : Γ') (x : SL(2, ℝ)) :
    ∑' γ : Γ', F ((γ : SL(2, ℝ)) * ((γ₁ : SL(2, ℝ)) * x)) = ∑' γ : Γ', F ((γ : SL(2, ℝ)) * x) := by
  refine Eq.trans ?_ (Equiv.tsum_eq (Equiv.mulRight γ₁) fun γ : Γ' => F ((γ : SL(2, ℝ)) * x))
  refine tsum_congr fun γ => ?_
  show F ((γ : SL(2, ℝ)) * ((γ₁ : SL(2, ℝ)) * x)) = F (((γ * γ₁ : Γ') : SL(2, ℝ)) * x)
  rw [Subgroup.coe_mul, mul_assoc]

/-- A.e. on `D`: `g ∈ D`, only `γ = 1` folds `g` into `D`, and exactly one `γ₀` folds `g h` into `D`. -/
theorem s19r_ae_good {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {Γ' : Subgroup SL(2, ℝ)} (hΓ' : LiZhongQC.IsFuchsian Γ')
    (hneg : -1 ∈ Γ')
    (hrel : ∀ M ∈ Γ', ∃ g ∈ Γ, ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I))
    (hrel' : ∀ g ∈ Γ, ∃ M ∈ Γ', ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I))
    (h : SL(2, ℝ)) :
    ∀ᵐ g ∂(s19rMeasure.restrict (s19rDomain Γ)), g ∈ s19rDomain Γ ∧
      (∀ γ : Γ', (γ : SL(2, ℝ)) * g ∈ s19rDomain Γ → γ = 1) ∧
      ∃ γ₀ : Γ', (γ₀ : SL(2, ℝ)) * g * h ∈ s19rDomain Γ ∧
        ∀ γ : Γ', (γ : SL(2, ℝ)) * g * h ∈ s19rDomain Γ → γ = γ₀ := by
  filter_upwards [ae_restrict_mem (s19r_dom_meas Γ), s19r_unique hΓ hΓ' hneg hrel hrel' h,
    s19r_unique hΓ hΓ' hneg hrel hrel' 1] with g hg h1 h2
  obtain ⟨γ₁, -, hγ₁⟩ := h2
  have h1g : ((1 : Γ') : SL(2, ℝ)) * g * 1 ∈ s19rDomain Γ := by
    show (1 : SL(2, ℝ)) * g * 1 ∈ s19rDomain Γ
    rw [one_mul, mul_one]
    exact hg
  refine ⟨hg, fun γ hγ => (hγ₁ γ (by simpa only [mul_one] using hγ)).trans (hγ₁ 1 h1g).symm, ?_⟩
  obtain ⟨γ₀, hγ₀, hu⟩ := h1
  exact ⟨γ₀, hγ₀, hu⟩

/-- The folded translate is a.e.-strongly measurable on `D`. -/
theorem s19r_fold_aesm {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {Γ' : Subgroup SL(2, ℝ)}
    (hΓ' : LiZhongQC.IsFuchsian Γ') (hneg : -1 ∈ Γ')
    (hrel : ∀ M ∈ Γ', ∃ g ∈ Γ, ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I))
    (hrel' : ∀ g ∈ Γ, ∃ M ∈ Γ', ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I))
    {φ : SL(2, ℝ) → ℝ} (hφ : AEStronglyMeasurable φ (s19rMeasure.restrict (s19rDomain Γ))) (h : SL(2, ℝ)) :
    AEStronglyMeasurable (fun g => ∑' γ : Γ', (s19rDomain Γ).indicator φ ((γ : SL(2, ℝ)) * g * h))
      (s19rMeasure.restrict (s19rDomain Γ)) := by
  haveI := s13c_countable hΓ'
  have hf : AEStronglyMeasurable ((s19rDomain Γ).indicator φ) s19rMeasure :=
    (aestronglyMeasurable_indicator_iff (s19r_dom_meas Γ)).mpr hφ
  have hterm : ∀ γ : Γ', AEStronglyMeasurable
      (fun g => (s19rDomain Γ).indicator φ ((γ : SL(2, ℝ)) * g * h)) (s19rMeasure.restrict (s19rDomain Γ)) :=
    fun γ => (hf.comp_measurePreserving ((MeasurePreserving.mk (s19r_mul_right_meas h) (s19r_right_inv h)).comp
      (MeasurePreserving.mk (s19r_mul_left_meas γ) (s19r_left_inv γ)))).restrict
  refine aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset Γ'))
    (f := fun s g => ∑ γ ∈ s, (s19rDomain Γ).indicator φ ((γ : SL(2, ℝ)) * g * h))
    (fun s => s.aestronglyMeasurable_fun_sum fun γ _ => hterm γ) ?_
  filter_upwards [s19r_ae_good hΓ hΓ' hneg hrel hrel' h] with g hg
  obtain ⟨-, -, γ₀, -, hu⟩ := hg
  have hs : Summable (fun γ : Γ' => (s19rDomain Γ).indicator φ ((γ : SL(2, ℝ)) * g * h)) :=
    summable_of_ne_finset_zero (s := {γ₀}) fun γ hγ =>
      indicator_of_notMem (fun hm => hγ (Finset.mem_singleton.mpr (hu γ hm))) _
  exact hs.hasSum

/-- **Isometry** of the folded right translate on `L²(μ|_D)`. -/
theorem s19r_iso {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {Γ' : Subgroup SL(2, ℝ)}
    (hΓ' : LiZhongQC.IsFuchsian Γ') (hneg : -1 ∈ Γ')
    (hrel : ∀ M ∈ Γ', ∃ g ∈ Γ, ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I))
    (hrel' : ∀ g ∈ Γ, ∃ M ∈ Γ', ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I))
    {φ : SL(2, ℝ) → ℝ} (hφ : MemLp φ 2 (s19rMeasure.restrict (s19rDomain Γ))) (h : SL(2, ℝ)) :
    MemLp (fun g => ∑' γ : Γ', (s19rDomain Γ).indicator φ ((γ : SL(2, ℝ)) * g * h)) 2
        (s19rMeasure.restrict (s19rDomain Γ)) ∧
      eLpNorm (fun g => ∑' γ : Γ', (s19rDomain Γ).indicator φ ((γ : SL(2, ℝ)) * g * h)) 2
        (s19rMeasure.restrict (s19rDomain Γ)) = eLpNorm φ 2 (s19rMeasure.restrict (s19rDomain Γ)) := by
  haveI := s13c_countable hΓ'
  haveI : SMulInvariantMeasure Γ' SL(2, ℝ) s19rMeasure := ⟨fun γ s hs => by
    show s19rMeasure ((fun x => (γ : SL(2, ℝ)) * x) ⁻¹' s) = s19rMeasure s
    rw [← Measure.map_apply (s19r_mul_left_meas γ) hs, s19r_left_inv]⟩
  have hfd := s19r_fd hΓ hneg hrel hrel'
  have hfdR := s19r_fd_right hΓ hneg hrel hrel' h
  have haes := s19r_fold_aesm hΓ hΓ' hneg hrel hrel' hφ.aestronglyMeasurable h
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : SL(2, ℝ) → ℝ,
      Φ = fun x => ∑' γ : Γ', (s19rDomain Γ).indicator φ ((γ : SL(2, ℝ)) * x) := ⟨_, rfl⟩
  have hΦx : ∀ x, Φ x = ∑' γ : Γ', (s19rDomain Γ).indicator φ ((γ : SL(2, ℝ)) * x) := fun x => by rw [hΦ]
  have hfold : ∀ g, ∑' γ : Γ', (s19rDomain Γ).indicator φ ((γ : SL(2, ℝ)) * g * h) = Φ (g * h) := fun g => by
    rw [hΦx]
    exact tsum_congr fun γ => by rw [mul_assoc]
  have hinv : ∀ (γ : Γ') (x : SL(2, ℝ)), ‖Φ (γ • x)‖ₑ ^ (2 : ℝ) = ‖Φ x‖ₑ ^ (2 : ℝ) := by
    intro γ x
    rw [hΦx, hΦx]
    show ‖∑' γ' : Γ', (s19rDomain Γ).indicator φ ((γ' : SL(2, ℝ)) * ((γ : SL(2, ℝ)) * x))‖ₑ ^ (2 : ℝ) = _
    rw [s19r_per_inv]
  have hmp : MeasurePreserving (· * h) s19rMeasure s19rMeasure := ⟨s19r_mul_right_meas h, s19r_right_inv h⟩
  have hemb : MeasurableEmbedding (· * h) := (Homeomorph.mulRight h).measurableEmbedding
  have e1 : ∫⁻ g in s19rDomain Γ, ‖Φ (g * h)‖ₑ ^ (2 : ℝ) ∂s19rMeasure =
      ∫⁻ x in (· * h) '' s19rDomain Γ, ‖Φ x‖ₑ ^ (2 : ℝ) ∂s19rMeasure :=
    hmp.setLIntegral_comp_emb hemb (fun x => ‖Φ x‖ₑ ^ (2 : ℝ)) _
  have e2 := hfdR.setLIntegral_eq hfd (fun x => ‖Φ x‖ₑ ^ (2 : ℝ)) hinv
  have e3 : ∫⁻ x in s19rDomain Γ, ‖Φ x‖ₑ ^ (2 : ℝ) ∂s19rMeasure =
      ∫⁻ x in s19rDomain Γ, ‖φ x‖ₑ ^ (2 : ℝ) ∂s19rMeasure := by
    refine lintegral_congr_ae ?_
    filter_upwards [s19r_ae_good hΓ hΓ' hneg hrel hrel' 1] with g hg
    obtain ⟨hgD, h1, -⟩ := hg
    rw [hΦx, s19r_tsum_single φ (fun γ : Γ' => (γ : SL(2, ℝ)) * g) 1 h1]
    show ‖(s19rDomain Γ).indicator φ (1 * g)‖ₑ ^ (2 : ℝ) = _
    rw [one_mul, indicator_of_mem hgD]
  have hnorm : eLpNorm (fun g => ∑' γ : Γ', (s19rDomain Γ).indicator φ ((γ : SL(2, ℝ)) * g * h)) 2
      (s19rMeasure.restrict (s19rDomain Γ)) = eLpNorm φ 2 (s19rMeasure.restrict (s19rDomain Γ)) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top haes,
      eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hφ.aestronglyMeasurable, ENNReal.toReal_ofNat]
    congr 1
    calc ∫⁻ g in s19rDomain Γ, ‖∑' γ : Γ', (s19rDomain Γ).indicator φ ((γ : SL(2, ℝ)) * g * h)‖ₑ ^ (2 : ℝ)
          ∂s19rMeasure
        = ∫⁻ g in s19rDomain Γ, ‖Φ (g * h)‖ₑ ^ (2 : ℝ) ∂s19rMeasure := lintegral_congr fun g => by rw [hfold]
      _ = _ := by rw [e1, e2, e3]
  exact ⟨by rw [memLp_iff, hnorm]; exact hφ, hnorm⟩

/-- **Right action**: folding twice is folding by the product. -/
theorem s19r_act {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {Γ' : Subgroup SL(2, ℝ)}
    (hΓ' : LiZhongQC.IsFuchsian Γ') (hneg : -1 ∈ Γ')
    (hrel : ∀ M ∈ Γ', ∃ g ∈ Γ, ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I))
    (hrel' : ∀ g ∈ Γ, ∃ M ∈ Γ', ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I))
    (φ : SL(2, ℝ) → ℝ) (h h' : SL(2, ℝ)) :
    (fun g => ∑' γ : Γ', (s19rDomain Γ).indicator
        (fun x => ∑' γ' : Γ', (s19rDomain Γ).indicator φ ((γ' : SL(2, ℝ)) * x * h)) ((γ : SL(2, ℝ)) * g * h'))
      =ᵐ[s19rMeasure.restrict (s19rDomain Γ)]
      fun g => ∑' γ : Γ', (s19rDomain Γ).indicator φ ((γ : SL(2, ℝ)) * g * (h' * h)) := by
  filter_upwards [s19r_ae_good hΓ hΓ' hneg hrel hrel' h'] with g hg
  obtain ⟨-, -, γ₀, hγ₀, hu⟩ := hg
  rw [s19r_tsum_single _ (fun γ : Γ' => (γ : SL(2, ℝ)) * g * h') γ₀ hu, indicator_of_mem hγ₀]
  have e : ∀ γ' : Γ', (γ' : SL(2, ℝ)) * ((γ₀ : SL(2, ℝ)) * g * h') * h =
      (γ' : SL(2, ℝ)) * ((γ₀ : SL(2, ℝ)) * (g * (h' * h))) := fun γ' => by simp only [mul_assoc]
  have e' : ∀ γ : Γ', (γ : SL(2, ℝ)) * g * (h' * h) = (γ : SL(2, ℝ)) * (g * (h' * h)) :=
    fun γ => mul_assoc _ _ _
  simp only [e, e']
  exact s19r_per_inv _ γ₀ _

/-- Folding by `1` is the identity a.e. on `D`. -/
theorem s19r_fold_one {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {Γ' : Subgroup SL(2, ℝ)}
    (hΓ' : LiZhongQC.IsFuchsian Γ') (hneg : -1 ∈ Γ')
    (hrel : ∀ M ∈ Γ', ∃ g ∈ Γ, ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I))
    (hrel' : ∀ g ∈ Γ, ∃ M ∈ Γ', ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I))
    (φ : SL(2, ℝ) → ℝ) :
    (fun g => ∑' γ : Γ', (s19rDomain Γ).indicator φ ((γ : SL(2, ℝ)) * g * 1))
      =ᵐ[s19rMeasure.restrict (s19rDomain Γ)] φ := by
  filter_upwards [s19r_ae_good hΓ hΓ' hneg hrel hrel' 1] with g hg
  obtain ⟨hgD, h1, -⟩ := hg
  rw [s19r_tsum_single φ (fun γ : Γ' => (γ : SL(2, ℝ)) * g * 1) 1
    fun γ hγ => h1 γ (by simpa only [mul_one] using hγ)]
  show (s19rDomain Γ).indicator φ (1 * g * 1) = φ g
  rw [one_mul, mul_one, indicator_of_mem hgD]

/-! ### Strong continuity of the folded translates (下属3) -/

/-- `s19rMeasure` is a regular measure (a σ-finite left-invariant measure, finite and positive on `K₀`). -/
theorem s19r_regular : s19rMeasure.Regular := by
  haveI : SigmaFinite s19rMeasure := s19r_sigma
  haveI : Measure.IsMulLeftInvariant s19rMeasure := ⟨s19r_left_inv⟩
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → ℝ))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℝ))
  haveI : LocallyCompactSpace SL(2, ℝ) :=
    Matrix.SpecialLinearGroup.isClosedEmbedding_val.locallyCompactSpace
  haveI : SecondCountableTopology SL(2, ℝ) :=
    Matrix.SpecialLinearGroup.isClosedEmbedding_val.isEmbedding.secondCountableTopology
  obtain ⟨K₀, -, hK0'⟩ := s19r_K0
  exact Measure.regular_of_isMulLeftInvariant K₀.isCompact K₀.interior_nonempty hK0'.ne

/-- Right translation preserves `s19rMeasure`. -/
theorem s19r_mp_right (h : SL(2, ℝ)) : MeasurePreserving (· * h) s19rMeasure s19rMeasure :=
  ⟨s19r_mul_right_meas h, s19r_right_inv h⟩

/-- Continuity of right translation in `L²(μ)` for continuous compactly supported functions. -/
theorem s19r_cc_cont {ψ : SL(2, ℝ) → ℝ} (hψ : Continuous ψ) (hs : HasCompactSupport ψ) :
    Tendsto (fun h : SL(2, ℝ) => ∫⁻ x, ‖ψ (x * h) - ψ x‖ₑ ^ (2 : ℝ) ∂s19rMeasure) (𝓝 1) (𝓝 0) := by
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → ℝ))
  haveI : LocallyCompactSpace SL(2, ℝ) :=
    Matrix.SpecialLinearGroup.isClosedEmbedding_val.locallyCompactSpace
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℝ))
  haveI : SecondCountableTopology SL(2, ℝ) :=
    Matrix.SpecialLinearGroup.isClosedEmbedding_val.isEmbedding.secondCountableTopology
  haveI : TopologicalSpace.MetrizableSpace (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (TopologicalSpace.MetrizableSpace (Fin 2 → Fin 2 → ℝ))
  haveI : TopologicalSpace.MetrizableSpace SL(2, ℝ) :=
    Matrix.SpecialLinearGroup.isClosedEmbedding_val.isEmbedding.metrizableSpace
  haveI := s19r_regular
  obtain ⟨C, hC⟩ := hψ.bounded_above_of_compact_support hs
  obtain ⟨W, hWc, hW1⟩ := exists_compact_mem_nhds (1 : SL(2, ℝ))
  obtain ⟨S, hS⟩ : ∃ S : Set SL(2, ℝ), S = (fun p : SL(2, ℝ) × SL(2, ℝ) => p.1 * p.2⁻¹) '' (tsupport ψ ×ˢ W) ∪
      tsupport ψ := ⟨_, rfl⟩
  have hSc : IsCompact S := by
    rw [hS]
    exact ((hs.prod hWc).image (by fun_prop)).union hs
  have hSm : MeasurableSet S := hSc.isClosed.measurableSet
  have hSfin : s19rMeasure S < ∞ := hSc.measure_lt_top
  have hzero : ∫⁻ _x : SL(2, ℝ), (0 : ℝ≥0∞) ∂s19rMeasure = 0 := lintegral_zero
  rw [← hzero]
  refine tendsto_lintegral_filter_of_dominated_convergence'
    (fun x => S.indicator (fun _ => ENNReal.ofReal ((2 * C) ^ 2)) x) ?_ ?_ ?_ ?_
  · refine Eventually.of_forall fun h => ?_
    have hc : Continuous fun x : SL(2, ℝ) => ψ (x * h) - ψ x := (hψ.comp (continuous_id.mul continuous_const)).sub hψ
    exact (ENNReal.continuous_rpow_const.comp hc.enorm).measurable.aemeasurable
  · filter_upwards [hW1] with h hh
    refine Eventually.of_forall fun x => ?_
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx]
      have h1 : ‖ψ (x * h) - ψ x‖ ≤ 2 * C := by
        calc ‖ψ (x * h) - ψ x‖ ≤ ‖ψ (x * h)‖ + ‖ψ x‖ := norm_sub_le _ _
          _ ≤ C + C := add_le_add (hC _) (hC _)
          _ = 2 * C := by ring
      have h2 : ‖ψ (x * h) - ψ x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖ψ (x * h) - ψ x‖ ^ 2) := by
        rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
        norm_cast
      rw [h2]
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) h1 2)
    · rw [indicator_of_notMem hx]
      have hx0 : x ∉ tsupport ψ := fun h' => hx (by rw [hS]; exact Or.inr h')
      have hxh : x * h ∉ tsupport ψ := by
        intro h'
        apply hx
        rw [hS]
        refine Or.inl ⟨(x * h, h), ⟨h', hh⟩, ?_⟩
        show x * h * h⁻¹ = x
        rw [mul_assoc, mul_inv_cancel, mul_one]
      rw [image_eq_zero_of_notMem_tsupport hx0, image_eq_zero_of_notMem_tsupport hxh, sub_zero, enorm_zero,
        ENNReal.zero_rpow_of_pos (by norm_num)]
  · rw [lintegral_indicator hSm, setLIntegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hSfin.ne
  · refine Eventually.of_forall fun x => ?_
    have hc : Continuous fun h : SL(2, ℝ) => ‖ψ (x * h) - ψ x‖ₑ ^ (2 : ℝ) :=
      ENNReal.continuous_rpow_const.comp ((hψ.comp (continuous_const.mul continuous_id)).sub continuous_const).enorm
    have h0 : ‖ψ (x * 1) - ψ x‖ₑ ^ (2 : ℝ) = 0 := by
      rw [mul_one, sub_self, enorm_zero, ENNReal.zero_rpow_of_pos (by norm_num)]
    have := hc.tendsto 1
    rwa [h0] at this

/-- `∫ ‖f‖ₑ² = eLpNorm f 2 ^ 2`. -/
theorem s19r_lint_sq {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : AEStronglyMeasurable f μ) :
    ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ = eLpNorm f 2 μ ^ (2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hf, ENNReal.toReal_ofNat,
    ← ENNReal.rpow_mul]
  norm_num

/-- Continuity of right translation in `L²(μ)`. -/
theorem s19r_L2_cont {u : SL(2, ℝ) → ℝ} (hu : MemLp u 2 s19rMeasure) :
    Tendsto (fun h : SL(2, ℝ) => eLpNorm (fun x => u (x * h) - u x) 2 s19rMeasure) (𝓝 1) (𝓝 0) := by
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → ℝ))
  haveI : LocallyCompactSpace SL(2, ℝ) :=
    Matrix.SpecialLinearGroup.isClosedEmbedding_val.locallyCompactSpace
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℝ))
  haveI : SecondCountableTopology SL(2, ℝ) :=
    Matrix.SpecialLinearGroup.isClosedEmbedding_val.isEmbedding.secondCountableTopology
  haveI : TopologicalSpace.MetrizableSpace (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (TopologicalSpace.MetrizableSpace (Fin 2 → Fin 2 → ℝ))
  haveI : TopologicalSpace.MetrizableSpace SL(2, ℝ) :=
    Matrix.SpecialLinearGroup.isClosedEmbedding_val.isEmbedding.metrizableSpace
  haveI := s19r_regular
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hε3 : ε / 3 ≠ 0 := (ENNReal.div_pos hε.ne' ENNReal.ofNat_ne_top).ne'
  obtain ⟨ψ, hψs, hψe, hψc, hψm⟩ := hu.exists_hasCompactSupport_eLpNorm_sub_le ENNReal.ofNat_ne_top hε3
  have hcc := s19r_cc_cont hψc hψs
  -- convert the lintegral limit into an `eLpNorm` limit
  have hcc' : Tendsto (fun h : SL(2, ℝ) => eLpNorm (fun x => ψ (x * h) - ψ x) 2 s19rMeasure) (𝓝 1) (𝓝 0) := by
    have hc2 : ∀ h : SL(2, ℝ), eLpNorm (fun x => ψ (x * h) - ψ x) 2 s19rMeasure =
        (∫⁻ x, ‖ψ (x * h) - ψ x‖ₑ ^ (2 : ℝ) ∂s19rMeasure) ^ (1 / (2 : ℝ)) := by
      intro h
      have hm : AEStronglyMeasurable (fun x => ψ (x * h) - ψ x) s19rMeasure :=
        ((hψc.comp (continuous_id.mul continuous_const)).sub hψc).aestronglyMeasurable
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hm, ENNReal.toReal_ofNat]
    simp only [hc2]
    have := (ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at this
    exact this.comp hcc
  filter_upwards [(ENNReal.tendsto_nhds_zero.mp hcc') (ε / 3) (ENNReal.div_pos hε.ne' ENNReal.ofNat_ne_top)]
    with h hh
  have hum := hu.aestronglyMeasurable
  have hψa := hψc.aestronglyMeasurable (μ := s19rMeasure)
  have htr : eLpNorm (fun x => u (x * h) - ψ (x * h)) 2 s19rMeasure = eLpNorm (u - ψ) 2 s19rMeasure := by
    have := eLpNorm_comp_measurePreserving (p := 2) (hum.sub hψa) (s19r_mp_right h)
    exact this
  have hsplit : (fun x => u (x * h) - u x) =
      (fun x => u (x * h) - ψ (x * h)) + (fun x => ψ (x * h) - ψ x) + (ψ - u) := by
    funext x
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have hψu : eLpNorm (ψ - u) 2 s19rMeasure = eLpNorm (u - ψ) 2 s19rMeasure := eLpNorm_sub_comm _ _ _ _
  have hm1 : AEStronglyMeasurable (fun x => u (x * h) - ψ (x * h)) s19rMeasure :=
    (hum.sub hψa).comp_measurePreserving (s19r_mp_right h)
  have hm2 : AEStronglyMeasurable (fun x => ψ (x * h) - ψ x) s19rMeasure :=
    ((hψc.comp (continuous_id.mul continuous_const)).sub hψc).aestronglyMeasurable
  rw [hsplit]
  calc eLpNorm ((fun x => u (x * h) - ψ (x * h)) + (fun x => ψ (x * h) - ψ x) + (ψ - u)) 2 s19rMeasure
      ≤ eLpNorm ((fun x => u (x * h) - ψ (x * h)) + (fun x => ψ (x * h) - ψ x)) 2 s19rMeasure +
          eLpNorm (ψ - u) 2 s19rMeasure := eLpNorm_add_le one_le_two
    _ ≤ eLpNorm (fun x => u (x * h) - ψ (x * h)) 2 s19rMeasure + eLpNorm (fun x => ψ (x * h) - ψ x) 2 s19rMeasure +
          eLpNorm (ψ - u) 2 s19rMeasure := by gcongr; exact eLpNorm_add_le one_le_two
    _ ≤ ε / 3 + ε / 3 + ε / 3 := by
          rw [htr, hψu]
          gcongr
    _ = ε := ENNReal.add_thirds ε

/-- **R3.** The folded right translate `fold φ h g = ∑' γ, 1_D(γ g h) φ(γ g h)` acts isometrically on `L²(μ|_D)`, as a
right action, and strongly continuously. -/
theorem s19r_rep {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {Γ' : Subgroup SL(2, ℝ)} (hΓ' : LiZhongQC.IsFuchsian Γ') (hneg : -1 ∈ Γ')
    (hrel : ∀ M ∈ Γ', ∃ g ∈ Γ, ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I))
    (hrel' : ∀ g ∈ Γ, ∃ M ∈ Γ', ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I))
    {φ : SL(2, ℝ) → ℝ} (hφ : MemLp φ 2 (s19rMeasure.restrict (s19rDomain Γ))) :
    (∀ h : SL(2, ℝ),
      MemLp (fun g => ∑' γ : Γ', (s19rDomain Γ).indicator φ ((γ : SL(2, ℝ)) * g * h)) 2
          (s19rMeasure.restrict (s19rDomain Γ)) ∧
        eLpNorm (fun g => ∑' γ : Γ', (s19rDomain Γ).indicator φ ((γ : SL(2, ℝ)) * g * h)) 2
            (s19rMeasure.restrict (s19rDomain Γ)) = eLpNorm φ 2 (s19rMeasure.restrict (s19rDomain Γ))) ∧
      (∀ h h' : SL(2, ℝ),
        (fun g => ∑' γ : Γ', (s19rDomain Γ).indicator
            (fun x => ∑' γ' : Γ', (s19rDomain Γ).indicator φ ((γ' : SL(2, ℝ)) * x * h)) ((γ : SL(2, ℝ)) * g * h'))
          =ᵐ[s19rMeasure.restrict (s19rDomain Γ)]
          fun g => ∑' γ : Γ', (s19rDomain Γ).indicator φ ((γ : SL(2, ℝ)) * g * (h' * h))) ∧
      (fun g => ∑' γ : Γ', (s19rDomain Γ).indicator φ ((γ : SL(2, ℝ)) * g * 1))
          =ᵐ[s19rMeasure.restrict (s19rDomain Γ)] φ ∧
      Tendsto (fun h : SL(2, ℝ) =>
          eLpNorm ((fun g => ∑' γ : Γ', (s19rDomain Γ).indicator φ ((γ : SL(2, ℝ)) * g * h)) - φ) 2
            (s19rMeasure.restrict (s19rDomain Γ))) (𝓝 1) (𝓝 0) := by
  haveI := s13c_countable hΓ'
  haveI : SMulInvariantMeasure Γ' SL(2, ℝ) s19rMeasure := ⟨fun γ s hs => by
    show s19rMeasure ((fun x => (γ : SL(2, ℝ)) * x) ⁻¹' s) = s19rMeasure s
    rw [← Measure.map_apply (s19r_mul_left_meas γ) hs, s19r_left_inv]⟩
  refine ⟨fun h => s19r_iso hΓ hΓ' hneg hrel hrel' hφ h, fun h h' => s19r_act hΓ hΓ' hneg hrel hrel' φ h h',
    s19r_fold_one hΓ hΓ' hneg hrel hrel' φ, ?_⟩
  -- strong continuity: fold back to the right translate of `f = 1_D φ` on `G`
  have hD := s19r_dom_meas Γ
  have hfd := s19r_fd hΓ hneg hrel hrel'
  obtain ⟨f, hf⟩ : ∃ f : SL(2, ℝ) → ℝ, f = (s19rDomain Γ).indicator φ := ⟨_, rfl⟩
  have hfm : MemLp f 2 s19rMeasure := by
    rw [hf]
    exact (memLp_indicator_iff_restrict hD).mpr hφ
  have hfa := hfm.aestronglyMeasurable
  have hL2 := s19r_L2_cont hfm
  -- the pointwise folding bound
  have hbound : ∀ h : SL(2, ℝ), ∀ᵐ g ∂(s19rMeasure.restrict (s19rDomain Γ)),
      ‖((fun g => ∑' γ : Γ', (s19rDomain Γ).indicator φ ((γ : SL(2, ℝ)) * g * h)) - φ) g‖ₑ ^ (2 : ℝ) ≤
        2 * ∑' γ : Γ', ‖f ((γ : SL(2, ℝ)) * g * h) - f ((γ : SL(2, ℝ)) * g)‖ₑ ^ (2 : ℝ) := by
    intro h
    filter_upwards [s19r_ae_good hΓ hΓ' hneg hrel hrel' h] with g hg
    obtain ⟨hgD, h1, γ₀, hγ₀, hu⟩ := hg
    have hfold : ∑' γ : Γ', (s19rDomain Γ).indicator φ ((γ : SL(2, ℝ)) * g * h) =
        f ((γ₀ : SL(2, ℝ)) * g * h) := by
      rw [s19r_tsum_single φ (fun γ : Γ' => (γ : SL(2, ℝ)) * g * h) γ₀ hu, hf]
    have hφg : φ g = f g := by rw [hf, indicator_of_mem hgD]
    show ‖∑' γ : Γ', (s19rDomain Γ).indicator φ ((γ : SL(2, ℝ)) * g * h) - φ g‖ₑ ^ (2 : ℝ) ≤ _
    rw [hfold, hφg]
    obtain ⟨U, hU⟩ : ∃ U : Γ' → ℝ≥0∞, U = fun γ : Γ' => ‖f ((γ : SL(2, ℝ)) * g * h) - f ((γ : SL(2, ℝ)) * g)‖ₑ ^ (2 : ℝ) :=
      ⟨_, rfl⟩
    have hUap : ∀ γ : Γ', U γ = ‖f ((γ : SL(2, ℝ)) * g * h) - f ((γ : SL(2, ℝ)) * g)‖ₑ ^ (2 : ℝ) :=
      fun γ => by rw [hU]
    rw [← hU]
    by_cases h0 : γ₀ = 1
    · have e : f ((γ₀ : SL(2, ℝ)) * g * h) - f g = f (((1 : Γ') : SL(2, ℝ)) * g * h) - f (((1 : Γ') : SL(2, ℝ)) * g) := by
        rw [h0]
        simp
      rw [e, ← hUap]
      calc U 1 ≤ ∑' γ : Γ', U γ := ENNReal.le_tsum 1
        _ ≤ 2 * ∑' γ : Γ', U γ := le_mul_of_one_le_left zero_le one_le_two
    · have hf1 : f ((γ₀ : SL(2, ℝ)) * g) = 0 := by
        rw [hf]
        exact indicator_of_notMem (fun hm => h0 (h1 γ₀ hm)) _
      have hf2 : f (g * h) = 0 := by
        rw [hf]
        refine indicator_of_notMem (fun hm => h0 (hu 1 ?_).symm) _
        show (1 : SL(2, ℝ)) * g * h ∈ s19rDomain Γ
        rw [one_mul]
        exact hm
      have e : f ((γ₀ : SL(2, ℝ)) * g * h) - f g =
          (f ((γ₀ : SL(2, ℝ)) * g * h) - f ((γ₀ : SL(2, ℝ)) * g)) +
            (f (((1 : Γ') : SL(2, ℝ)) * g * h) - f (((1 : Γ') : SL(2, ℝ)) * g)) := by
        simp only [Subgroup.coe_one, one_mul, hf1, hf2]
        ring
      rw [e]
      calc ‖(f ((γ₀ : SL(2, ℝ)) * g * h) - f ((γ₀ : SL(2, ℝ)) * g)) +
              (f (((1 : Γ') : SL(2, ℝ)) * g * h) - f (((1 : Γ') : SL(2, ℝ)) * g))‖ₑ ^ (2 : ℝ)
          ≤ (‖f ((γ₀ : SL(2, ℝ)) * g * h) - f ((γ₀ : SL(2, ℝ)) * g)‖ₑ +
              ‖f (((1 : Γ') : SL(2, ℝ)) * g * h) - f (((1 : Γ') : SL(2, ℝ)) * g)‖ₑ) ^ (2 : ℝ) :=
            ENNReal.rpow_le_rpow (enorm_add_le _ _) (by norm_num)
        _ ≤ 2 ^ ((2 : ℝ) - 1) * (U γ₀ + U 1) := by
            rw [hUap, hUap]
            exact ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ (by norm_num)
        _ = 2 * ∑ γ ∈ ({γ₀, 1} : Finset Γ'), U γ := by
            rw [Finset.sum_pair h0]
            norm_num
        _ ≤ 2 * ∑' γ : Γ', U γ := by
            gcongr
            exact ENNReal.sum_le_tsum _
  -- integrate the bound: `∫_D ∑'γ ‖u(γ g)‖² = ∫_G ‖u‖²`
  have hint : ∀ h : SL(2, ℝ), ∫⁻ g in s19rDomain Γ,
      ‖((fun g => ∑' γ : Γ', (s19rDomain Γ).indicator φ ((γ : SL(2, ℝ)) * g * h)) - φ) g‖ₑ ^ (2 : ℝ) ∂s19rMeasure ≤
        2 * ∫⁻ x, ‖f (x * h) - f x‖ₑ ^ (2 : ℝ) ∂s19rMeasure := by
    intro h
    have hum : AEStronglyMeasurable (fun x => f (x * h) - f x) s19rMeasure :=
      (hfa.comp_measurePreserving (s19r_mp_right h)).sub hfa
    have hterm : ∀ γ : Γ', AEMeasurable (fun g => ‖f ((γ : SL(2, ℝ)) * g * h) - f ((γ : SL(2, ℝ)) * g)‖ₑ ^ (2 : ℝ))
        (s19rMeasure.restrict (s19rDomain Γ)) := by
      intro γ
      have h1 := hum.comp_measurePreserving
        (MeasurePreserving.mk (s19r_mul_left_meas (γ : SL(2, ℝ))) (s19r_left_inv (γ : SL(2, ℝ))))
      exact ((h1.enorm.pow_const (2 : ℝ))).restrict
    calc _ ≤ ∫⁻ g in s19rDomain Γ, 2 * ∑' γ : Γ', ‖f ((γ : SL(2, ℝ)) * g * h) - f ((γ : SL(2, ℝ)) * g)‖ₑ ^ (2 : ℝ)
          ∂s19rMeasure := lintegral_mono_ae (hbound h)
      _ = 2 * ∑' γ : Γ', ∫⁻ g in s19rDomain Γ, ‖f ((γ : SL(2, ℝ)) * g * h) - f ((γ : SL(2, ℝ)) * g)‖ₑ ^ (2 : ℝ)
          ∂s19rMeasure := by
        rw [lintegral_const_mul' _ _ ENNReal.ofNat_ne_top, lintegral_tsum hterm]
      _ = 2 * ∫⁻ x, ‖f (x * h) - f x‖ₑ ^ (2 : ℝ) ∂s19rMeasure := by
        rw [hfd.lintegral_eq_tsum'' (fun x => ‖f (x * h) - f x‖ₑ ^ (2 : ℝ))]
        rfl
  -- conclude
  have hJ : Tendsto (fun h : SL(2, ℝ) => 2 * ∫⁻ x, ‖f (x * h) - f x‖ₑ ^ (2 : ℝ) ∂s19rMeasure) (𝓝 1) (𝓝 0) := by
    have e : ∀ h : SL(2, ℝ), ∫⁻ x, ‖f (x * h) - f x‖ₑ ^ (2 : ℝ) ∂s19rMeasure =
        eLpNorm (fun x => f (x * h) - f x) 2 s19rMeasure ^ (2 : ℝ) := fun h =>
      s19r_lint_sq ((hfa.comp_measurePreserving (s19r_mp_right h)).sub hfa)
    simp only [e]
    have h2 := (ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto 0
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h2
    have h3 := ENNReal.Tendsto.const_mul (a := (2 : ℝ≥0∞)) (h2.comp hL2) (Or.inr ENNReal.ofNat_ne_top)
    rw [mul_zero] at h3
    exact h3
  have hJ' : Tendsto (fun h : SL(2, ℝ) =>
      (2 * ∫⁻ x, ‖f (x * h) - f x‖ₑ ^ (2 : ℝ) ∂s19rMeasure) ^ (1 / (2 : ℝ))) (𝓝 1) (𝓝 0) := by
    have h2 := (ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h2
    exact h2.comp hJ
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hJ' (fun _ => zero_le) fun h => ?_
  have haes : AEStronglyMeasurable ((fun g => ∑' γ : Γ', (s19rDomain Γ).indicator φ ((γ : SL(2, ℝ)) * g * h)) - φ)
      (s19rMeasure.restrict (s19rDomain Γ)) :=
    (s19r_fold_aesm hΓ hΓ' hneg hrel hrel' hφ.aestronglyMeasurable h).sub hφ.aestronglyMeasurable
  show eLpNorm _ 2 _ ≤ _
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top haes, ENNReal.toReal_ofNat]
  exact ENNReal.rpow_le_rpow (hint h) (by norm_num)

open scoped Pointwise in
/-- **R4 (E).** Fold-invariant `L²(μ|_D)` functions are a.e. constant: their `Γ'`-periodization is a.e. right-invariant
under every `h`, hence (Fubini on `G × G`, left invariance of `μ`) a.e. constant. -/
theorem s19r4_erg {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {Γ' : Subgroup SL(2, ℝ)} (hΓ' : LiZhongQC.IsFuchsian Γ')
    (hneg : -1 ∈ Γ')
    (hrel : ∀ M ∈ Γ', ∃ g ∈ Γ, ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I))
    (hrel' : ∀ g ∈ Γ, ∃ M ∈ Γ', ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I))
    {φ : SL(2, ℝ) → ℝ} (hφ : MemLp φ 2 (s19rMeasure.restrict (s19rDomain Γ)))
    (hfix : ∀ h : SL(2, ℝ), (fun g => ∑' γ : Γ', (s19rDomain Γ).indicator φ ((γ : SL(2, ℝ)) * g * h))
        =ᵐ[s19rMeasure.restrict (s19rDomain Γ)] φ) :
    ∃ c : ℝ, φ =ᵐ[s19rMeasure.restrict (s19rDomain Γ)] fun _ => c := by
  obtain ⟨hμl, hμr, hσ, -⟩ := s19r_haar
  obtain ⟨hDm, hFD, -, -⟩ := s19r_domain hΓ hΓ' hneg hrel hrel'
  haveI : Countable Γ' := s13c_countable hΓ'
  haveI : SigmaFinite s19rMeasure := hσ
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℝ))
  haveI : SecondCountableTopology SL(2, ℝ) :=
    (Matrix.SpecialLinearGroup.isClosedEmbedding_val (n := Fin 2) (R := ℝ)).isInducing.secondCountableTopology
  set μ := s19rMeasure with hμdef
  set D := s19rDomain Γ with hDdef
  by_cases hμ0 : μ = 0
  · refine ⟨0, ?_⟩
    rw [hμ0, Measure.restrict_zero, Filter.EventuallyEq, ae_zero]
    exact Filter.eventually_bot
  have hlmp : ∀ a : SL(2, ℝ), MeasurePreserving (a * ·) μ μ := fun a => ⟨measurable_const_mul a, hμl a⟩
  have hrmp : ∀ a : SL(2, ℝ), MeasurePreserving (· * a) μ μ := fun a => ⟨measurable_mul_const a, hμr a⟩
  -- a measurable representative
  set φ' := hφ.aestronglyMeasurable.mk φ with hφ'def
  have hφ'm : Measurable φ' := hφ.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hφφ' : ∀ᵐ x ∂μ, x ∈ D → φ x = φ' x := (ae_restrict_iff' hDm).mp hφ.aestronglyMeasurable.ae_eq_mk
  -- at most one tile
  have hD1 : IsFundamentalDomain Γ' D μ := by
    have h := hFD 1
    simp only [mul_one, image_id'] at h
    exact h
  have hmem : ∀ (γ : Γ') (x : SL(2, ℝ)), (γ : SL(2, ℝ)) * x ∈ D ↔ x ∈ γ⁻¹ • D := fun γ x => by
    rw [mem_smul_set_iff_inv_smul_mem, inv_inv]
    rfl
  have hgood : ∀ᵐ x ∂μ, ∀ γ₁ γ₂ : Γ', (γ₁ : SL(2, ℝ)) * x ∈ D → (γ₂ : SL(2, ℝ)) * x ∈ D → γ₁ = γ₂ := by
    refine ae_all_iff.mpr fun γ₁ => ae_all_iff.mpr fun γ₂ => ?_
    by_cases he : γ₁ = γ₂
    · exact Eventually.of_forall fun _ _ _ => he
    · have hdis := hD1.aedisjoint (show γ₁⁻¹ ≠ γ₂⁻¹ from fun h => he (inv_injective h))
      have hnull : μ (γ₁⁻¹ • D ∩ γ₂⁻¹ • D) = 0 := hdis
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with x hx h1 h2
      exact absurd ⟨(hmem γ₁ x).mp h1, (hmem γ₂ x).mp h2⟩ hx
  -- the periodization and its measurable version
  set Φ : SL(2, ℝ) → ℝ := fun x => ∑' γ : Γ', D.indicator φ' ((γ : SL(2, ℝ)) * x) with hΦdef
  set Ψ : SL(2, ℝ) → ℝ := fun x =>
    (∑' γ : Γ', ENNReal.ofReal (D.indicator φ' ((γ : SL(2, ℝ)) * x))).toReal -
      (∑' γ : Γ', ENNReal.ofReal (-D.indicator φ' ((γ : SL(2, ℝ)) * x))).toReal with hΨdef
  have hind : ∀ γ : Γ', Measurable fun x : SL(2, ℝ) => D.indicator φ' ((γ : SL(2, ℝ)) * x) :=
    fun γ => (hφ'm.indicator hDm).comp (measurable_const_mul _)
  have hΨm : Measurable Ψ :=
    (ENNReal.measurable_toReal.comp (Measurable.ennreal_tsum fun γ => ENNReal.measurable_ofReal.comp (hind γ))).sub
      (ENNReal.measurable_toReal.comp (Measurable.ennreal_tsum fun γ =>
        ENNReal.measurable_ofReal.comp (hind γ).neg))
  -- values at a good point
  have hvals : ∀ x, (∀ γ₁ γ₂ : Γ', (γ₁ : SL(2, ℝ)) * x ∈ D → (γ₂ : SL(2, ℝ)) * x ∈ D → γ₁ = γ₂) →
      Φ x = Ψ x ∧ ∀ γ₀ : Γ', (γ₀ : SL(2, ℝ)) * x ∈ D → Φ x = φ' ((γ₀ : SL(2, ℝ)) * x) := by
    intro x hx
    by_cases hex : ∃ γ₀ : Γ', (γ₀ : SL(2, ℝ)) * x ∈ D
    · obtain ⟨γ₀, hγ₀⟩ := hex
      have hz : ∀ γ : Γ', γ ≠ γ₀ → D.indicator φ' ((γ : SL(2, ℝ)) * x) = 0 := fun γ hγ =>
        indicator_of_notMem (fun h => hγ (hx γ γ₀ h hγ₀)) _
      have hΦ : Φ x = φ' ((γ₀ : SL(2, ℝ)) * x) := by
        rw [hΦdef]
        simp only
        rw [tsum_eq_single γ₀ hz, indicator_of_mem hγ₀]
      refine ⟨?_, fun γ₁ hγ₁ => by rw [hΦ, hx γ₁ γ₀ hγ₁ hγ₀]⟩
      rw [hΦ, hΨdef]
      simp only
      rw [tsum_eq_single γ₀ (fun γ hγ => by rw [hz γ hγ, ENNReal.ofReal_zero]),
        tsum_eq_single γ₀ (fun γ hγ => by rw [hz γ hγ, neg_zero, ENNReal.ofReal_zero]),
        indicator_of_mem hγ₀, ENNReal.toReal_ofReal', ENNReal.toReal_ofReal']
      rcases le_total (φ' ((γ₀ : SL(2, ℝ)) * x)) 0 with h | h
      · rw [max_eq_right h, max_eq_left (by linarith)]
        ring
      · rw [max_eq_left h, max_eq_right (by linarith)]
        ring
    · push_neg at hex
      have hz : ∀ γ : Γ', D.indicator φ' ((γ : SL(2, ℝ)) * x) = 0 := fun γ => indicator_of_notMem (hex γ) _
      refine ⟨?_, fun γ₀ h => absurd h (hex γ₀)⟩
      rw [hΦdef, hΨdef]
      simp only [hz, ENNReal.ofReal_zero, neg_zero, tsum_zero, ENNReal.toReal_zero, sub_zero]
  have hΦΨ : ∀ᵐ x ∂μ, Φ x = Ψ x := hgood.mono fun x hx => (hvals x hx).1
  -- `Φ` is `Γ'`-periodic everywhere
  have hper : ∀ (γ₀ : Γ') (x : SL(2, ℝ)), Φ ((γ₀ : SL(2, ℝ)) * x) = Φ x := by
    intro γ₀ x
    rw [hΦdef]
    simp only
    have := (Equiv.mulRight γ₀).tsum_eq (fun γ : Γ' => D.indicator φ' ((γ : SL(2, ℝ)) * x))
    rw [← this]
    simp only [Equiv.coe_mulRight, Subgroup.coe_mul, mul_assoc]
  -- the fixing hypothesis transferred to `Φ` on `D`
  have hfixΦ : ∀ h : SL(2, ℝ), ∀ᵐ g ∂μ, g ∈ D → Φ (g * h) = Φ g := by
    intro h
    have h1 : ∀ᵐ g ∂μ, g ∈ D → (∑' γ : Γ', D.indicator φ ((γ : SL(2, ℝ)) * g * h)) = φ g :=
      (ae_restrict_iff' hDm).mp (hfix h)
    have h2 : ∀ᵐ g ∂μ, ∀ γ : Γ', (γ : SL(2, ℝ)) * g * h ∈ D →
        φ ((γ : SL(2, ℝ)) * g * h) = φ' ((γ : SL(2, ℝ)) * g * h) := by
      refine ae_all_iff.mpr fun γ => ?_
      have := ((hlmp γ).comp (hrmp h)).quasiMeasurePreserving.ae hφφ'
      filter_upwards [this] with g hg
      simpa only [Function.comp, mul_assoc] using hg
    filter_upwards [h1, h2, hφφ', hgood] with g hg1 hg2 hg3 hg4 hgD
    have hfold : (∑' γ : Γ', D.indicator φ ((γ : SL(2, ℝ)) * g * h)) = Φ (g * h) := by
      rw [hΦdef]
      simp only
      congr 1
      funext γ
      by_cases hm : (γ : SL(2, ℝ)) * g * h ∈ D
      · rw [indicator_of_mem hm, ← mul_assoc, indicator_of_mem hm, hg2 γ hm]
      · rw [indicator_of_notMem hm, ← mul_assoc, indicator_of_notMem hm]
    have hΦg : Φ g = φ' g := by
      have := (hvals g hg4).2 1 (by simpa using hgD)
      simpa using this
    rw [← hfold, hg1 hgD, hΦg, hg3 hgD]
  -- extended to `G` by periodicity and covering
  have hfixG : ∀ h : SL(2, ℝ), ∀ᵐ x ∂μ, Ψ (x * h) = Ψ x := by
    intro h
    have hcov : ∀ᵐ x ∂μ, ∃ γ : Γ', γ • x ∈ D := hD1.ae_covers
    have hall : ∀ᵐ x ∂μ, ∀ γ : Γ', (γ : SL(2, ℝ)) * x ∈ D →
        Φ ((γ : SL(2, ℝ)) * x * h) = Φ ((γ : SL(2, ℝ)) * x) :=
      ae_all_iff.mpr fun γ => (hlmp γ).quasiMeasurePreserving.ae (hfixΦ h)
    have hΦΨh : ∀ᵐ x ∂μ, Φ (x * h) = Ψ (x * h) := (hrmp h).quasiMeasurePreserving.ae hΦΨ
    filter_upwards [hcov, hall, hΦΨ, hΦΨh] with x hx1 hx2 hx3 hx4
    obtain ⟨γ, hγ⟩ := hx1
    have hγ' : (γ : SL(2, ℝ)) * x ∈ D := hγ
    have := hx2 γ hγ'
    rw [mul_assoc, hper, hper] at this
    rw [← hx3, ← hx4, this]
  -- Fubini on `G × G`
  have hS : MeasurableSet {p : SL(2, ℝ) × SL(2, ℝ) | Ψ (p.2 * p.1) = Ψ p.2} :=
    measurableSet_eq_fun (hΨm.comp (measurable_snd.mul measurable_fst)) (hΨm.comp measurable_snd)
  have hswap : ∀ᵐ x ∂μ, ∀ᵐ h ∂μ, Ψ (x * h) = Ψ x :=
    (Measure.ae_ae_comm hS).mp (Eventually.of_forall fun h => hfixG h)
  haveI : (ae μ).NeBot := ae_neBot.mpr hμ0
  obtain ⟨x₀, hx₀⟩ := hswap.exists
  have hconst : ∀ᵐ y ∂μ, Ψ y = Ψ x₀ := by
    have := (hlmp x₀⁻¹).quasiMeasurePreserving.ae hx₀
    filter_upwards [this] with y hy
    simpa only [mul_inv_cancel_left] using hy
  refine ⟨Ψ x₀, ?_⟩
  have hc' : ∀ᵐ y ∂μ, y ∈ D → φ y = Ψ x₀ := by
    filter_upwards [hconst, hΦΨ, hφφ', hgood] with y h1 h2 h3 h4 hyD
    have hΦy : Φ y = φ' y := by
      have := (hvals y h4).2 1 (by simpa using hyD)
      simpa using this
    rw [h3 hyD, ← hΦy, h2, h1]
  exact (ae_restrict_iff' hDm).mpr hc'

/-- The action of `SL(2, ℝ)` on `ℍ` in coordinates. -/
theorem s19r4_act (g : SL(2, ℝ)) (ξ : ℍ) :
    ((g • ξ : ℍ) : ℂ) = ((g 0 0 : ℂ) * ξ + g 0 1) / ((g 1 0 : ℂ) * ξ + g 1 1) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp

/-- The entries of `g_τ k_θ`. -/
theorem s19r4_iw_entries (p : ℍ × ℝ) :
    (s19rIwasawa p) 0 0 = √p.1.im * Real.cos p.2 + p.1.re / √p.1.im * Real.sin p.2 ∧
      (s19rIwasawa p) 0 1 = -(√p.1.im * Real.sin p.2) + p.1.re / √p.1.im * Real.cos p.2 ∧
      (s19rIwasawa p) 1 0 = 1 / √p.1.im * Real.sin p.2 ∧ (s19rIwasawa p) 1 1 = 1 / √p.1.im * Real.cos p.2 := by
  have hM : ((s19rIwasawa p : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![√p.1.im, p.1.re / √p.1.im; 0, 1 / √p.1.im] *
        !![Real.cos p.2, -Real.sin p.2; Real.sin p.2, Real.cos p.2] := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · show ((s19rIwasawa p : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = _
    rw [hM]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  · show ((s19rIwasawa p : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = _
    rw [hM]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  · show ((s19rIwasawa p : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = _
    rw [hM]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  · show ((s19rIwasawa p : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = _
    rw [hM]
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- `g_τ k_θ • i = τ`. -/
theorem s19r4_iw_act (p : ℍ × ℝ) : ((s19rIwasawa p • UpperHalfPlane.I : ℍ) : ℂ) = p.1 := by
  obtain ⟨e00, e01, e10, e11⟩ := s19r4_iw_entries p
  rw [s19r4_act, e00, e01, e10, e11, UpperHalfPlane.coe_I]
  have hy := p.1.im_pos
  have hs : 0 < √p.1.im := Real.sqrt_pos.mpr hy
  have hs2 : (√p.1.im) ^ 2 = p.1.im := Real.sq_sqrt hy.le
  have hcs := Real.sin_sq_add_cos_sq p.2
  have hden : ((1 / √p.1.im * Real.sin p.2 : ℝ) : ℂ) * I + ((1 / √p.1.im * Real.cos p.2 : ℝ) : ℂ) ≠ 0 := by
    intro h0
    have h1 := congrArg Complex.re h0
    have h2 := congrArg Complex.im h0
    simp at h1 h2
    have hs' : √p.1.im ≠ 0 := hs.ne'
    have hc0 : Real.cos p.2 = 0 := by
      rcases h1 with h1 | h1
      · exact absurd h1 (by positivity)
      · exact h1
    have hs0 : Real.sin p.2 = 0 := by
      rcases h2 with h2 | h2
      · exact absurd h2 (by positivity)
      · exact h2
    rw [hc0, hs0] at hcs
    norm_num at hcs
  rw [div_eq_iff hden]
  have hτ : (p.1 : ℂ) = (p.1.re : ℂ) + (p.1.im : ℂ) * I := (Complex.re_add_im _).symm
  have hsC : ((√p.1.im : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  have hs2C : ((√p.1.im : ℝ) : ℂ) ^ 2 = (p.1.im : ℂ) := by exact_mod_cast hs2
  rw [hτ, ← hs2C]
  set c := Real.cos p.2
  set sn := Real.sin p.2
  set r := √p.1.im
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- For `θ ∈ [0, 2π)`: `sin θ > 0 ∨ (sin θ = 0 ∧ cos θ > 0)` iff `θ < π`. -/
theorem s19r4_trig {θ : ℝ} (hθ : θ ∈ Ico 0 (2 * π)) :
    (0 < Real.sin θ ∨ (Real.sin θ = 0 ∧ 0 < Real.cos θ)) ↔ θ < π := by
  constructor
  · rintro (h | ⟨h1, h2⟩)
    · by_contra hle
      push_neg at hle
      have : 0 ≤ Real.sin (θ - π) := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [hθ.2])
      rw [Real.sin_sub_pi] at this
      linarith
    · by_contra hle
      push_neg at hle
      rcases eq_or_lt_of_le hle with heq | hlt
      · rw [← heq, Real.cos_pi] at h2
        linarith
      · have : 0 < Real.sin (θ - π) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hθ.2])
        rw [Real.sin_sub_pi] at this
        linarith
  · intro h
    rcases eq_or_lt_of_le hθ.1 with h0 | hpos
    · right
      rw [← h0, Real.sin_zero, Real.cos_zero]
      exact ⟨rfl, one_pos⟩
    · left
      exact Real.sin_pos_of_pos_of_lt_pi hpos h

/-- `g_τ k_θ ∈ D` iff `C(τ) ∈ F` and `θ ∈ [0, π)` (for `θ ∈ [0, 2π)`). -/
theorem s19r4_iw_mem {Γ : Subgroup SL2C} (τ : ℍ) {θ : ℝ} (hθ : θ ∈ Ico 0 (2 * π)) :
    s19rIwasawa (τ, θ) ∈ s19rDomain Γ ↔ ((τ : ℂ) + I) / ((τ : ℂ) - I) ∈ fundDomain Γ ∧ θ < π := by
  obtain ⟨-, -, e10, e11⟩ := s19r4_iw_entries (τ, θ)
  have hp : 0 < 1 / √τ.im := by have := Real.sqrt_pos.mpr τ.im_pos; positivity
  simp only [s19rDomain, Set.mem_setOf_eq]
  rw [s19r4_iw_act, e10, e11]
  refine and_congr_right fun _ => ?_
  rw [← s19r4_trig hθ, mul_pos_iff_of_pos_left hp, mul_pos_iff_of_pos_left hp, mul_eq_zero]
  simp only [hp.ne', false_or]

/-- `a⁻¹ • i = i (1+u)/(1-u)` for `a = mautnerDiag √((1-u)/(1+u))`. -/
theorem s19r4_inv_diag {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    (((mautnerDiag (√((1 - u) / (1 + u))))⁻¹ • UpperHalfPlane.I : ℍ) : ℂ) = I * (((1 + u) / (1 - u) : ℝ) : ℂ) := by
  have hq : 0 < (1 - u) / (1 + u) := div_pos (by linarith [hu.2]) (by linarith [hu.1])
  have hs : √((1 - u) / (1 + u)) ≠ 0 := (Real.sqrt_pos.mpr hq).ne'
  have hd : mautnerDiag (√((1 - u) / (1 + u))) = Matrix.SpecialLinearGroup.diag2 _ hs := dif_pos hs
  have hM : (((mautnerDiag (√((1 - u) / (1 + u))))⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(√((1 - u) / (1 + u)))⁻¹, 0; 0, √((1 - u) / (1 + u))] := by
    rw [hd, Matrix.SpecialLinearGroup.coe_inv, Matrix.SpecialLinearGroup.diag2_coe, Matrix.adjugate_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [s19r4_act]
  have e00 : (((mautnerDiag (√((1 - u) / (1 + u))))⁻¹ : SL(2, ℝ)) 0 0 : ℝ) = (√((1 - u) / (1 + u)))⁻¹ := by
    show (((mautnerDiag (√((1 - u) / (1 + u))))⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = _
    rw [hM]; simp
  have e01 : (((mautnerDiag (√((1 - u) / (1 + u))))⁻¹ : SL(2, ℝ)) 0 1 : ℝ) = 0 := by
    show (((mautnerDiag (√((1 - u) / (1 + u))))⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = _
    rw [hM]; simp
  have e10 : (((mautnerDiag (√((1 - u) / (1 + u))))⁻¹ : SL(2, ℝ)) 1 0 : ℝ) = 0 := by
    show (((mautnerDiag (√((1 - u) / (1 + u))))⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = _
    rw [hM]; simp
  have e11 : (((mautnerDiag (√((1 - u) / (1 + u))))⁻¹ : SL(2, ℝ)) 1 1 : ℝ) = √((1 - u) / (1 + u)) := by
    show (((mautnerDiag (√((1 - u) / (1 + u))))⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = _
    rw [hM]; simp
  rw [e00, e01, e10, e11, UpperHalfPlane.coe_I]
  have hsq : (√((1 - u) / (1 + u))) ^ 2 = (1 - u) / (1 + u) := Real.sq_sqrt hq.le
  have hsC : ((√((1 - u) / (1 + u)) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs
  have hsqC : ((√((1 - u) / (1 + u)) : ℝ) : ℂ) ^ 2 = (((1 - u) / (1 + u) : ℝ) : ℂ) := by exact_mod_cast hsq
  have h1 : (1 : ℂ) - u ≠ 0 := by exact_mod_cast (show (1 : ℝ) - u ≠ 0 by linarith [hu.2])
  have h2 : (1 : ℂ) + u ≠ 0 := by exact_mod_cast (show (1 : ℝ) + u ≠ 0 by linarith [hu.1])
  simp only [Complex.ofReal_zero, mul_zero, add_zero, zero_mul, zero_add, Complex.ofReal_inv]
  rw [show ((√((1 - u) / (1 + u)) : ℝ) : ℂ)⁻¹ * I / ((√((1 - u) / (1 + u)) : ℝ) : ℂ) =
      I / ((√((1 - u) / (1 + u)) : ℝ) : ℂ) ^ 2 by ring, hsqC]
  push_cast
  field_simp

/-- `g_τ k_θ = g_τ · k_θ` with `g_τ = s19rIwasawa (τ, 0)` and `k_θ = s19rIwasawa (i, θ)`. -/
theorem s19r4_iw_split (τ : ℍ) (θ : ℝ) :
    s19rIwasawa (τ, θ) = s19rIwasawa (τ, 0) * s19rIwasawa (UpperHalfPlane.I, θ) := by
  obtain ⟨a00, a01, a10, a11⟩ := s19r4_iw_entries (τ, θ)
  obtain ⟨b00, b01, b10, b11⟩ := s19r4_iw_entries (τ, 0)
  obtain ⟨c00, c01, c10, c11⟩ := s19r4_iw_entries (UpperHalfPlane.I, θ)
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  simp only [UpperHalfPlane.I_re, UpperHalfPlane.I_im, Real.sqrt_one, Real.cos_zero, Real.sin_zero] at *
  fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue] <;>
    simp only [a00, a01, a10, a11, b00, b01, b10, b11, c00, c01, c10, c11] <;> ring

/-- The rotation `k_θ` acts on the Cayley picture by the multiplier `(cos θ + i sin θ)²`. -/
theorem s19r4_rot (θ : ℝ) (w : ℍ) (hw : (w : ℂ) ≠ I) :
    (((s19rIwasawa (UpperHalfPlane.I, θ) • w : ℍ) : ℂ) + I) / (((s19rIwasawa (UpperHalfPlane.I, θ) • w : ℍ) : ℂ) - I) =
      ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I) ^ 2 * (((w : ℂ) + I) / ((w : ℂ) - I)) := by
  obtain ⟨e00, e01, e10, e11⟩ := s19r4_iw_entries (UpperHalfPlane.I, θ)
  simp only [UpperHalfPlane.I_re, UpperHalfPlane.I_im, Real.sqrt_one, div_one, one_mul, zero_mul, zero_div,
    add_zero, zero_add] at e00 e01 e10 e11
  rw [s19r4_act, e00, e01, e10, e11]
  have hcs := Real.sin_sq_add_cos_sq θ
  set c : ℂ := ((Real.cos θ : ℝ) : ℂ) with hc
  set s : ℂ := ((Real.sin θ : ℝ) : ℂ) with hs
  have hcsC : s ^ 2 + c ^ 2 = 1 := by rw [hc, hs]; exact_mod_cast hcs
  have hden : s * w + c ≠ 0 := by
    intro h0
    have him := congrArg Complex.im h0
    have hre := congrArg Complex.re h0
    simp only [hc, hs, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      add_zero, Complex.zero_im, Complex.add_re, Complex.mul_re, sub_zero, Complex.zero_re] at him hre
    have hs0 : Real.sin θ = 0 := by
      rcases mul_eq_zero.mp him with h | h
      · exact h
      · exact absurd h w.im_pos.ne'
    rw [hs0, zero_mul, zero_add] at hre
    rw [hs0, hre] at hcs
    norm_num at hcs
  have hwi : (w : ℂ) - I ≠ 0 := sub_ne_zero.mpr hw
  have hcc : (c + s * I) * (c - s * I) = 1 := by linear_combination hcsC - s ^ 2 * Complex.I_sq
  have hinv : (c - s * I)⁻¹ = c + s * I := inv_eq_of_mul_eq_one_right (by rw [mul_comm]; exact hcc)
  have hn : (c * w + ((-Real.sin θ : ℝ) : ℂ)) / (s * w + c) + I = (c + s * I) * (w + I) / (s * w + c) := by
    rw [Complex.ofReal_neg, ← hs, eq_div_iff hden, add_mul, div_mul_cancel₀ _ hden]
    linear_combination (-s) * Complex.I_sq
  have hd : (c * w + ((-Real.sin θ : ℝ) : ℂ)) / (s * w + c) - I = (c - s * I) * (w - I) / (s * w + c) := by
    rw [Complex.ofReal_neg, ← hs, eq_div_iff hden, sub_mul, div_mul_cancel₀ _ hden]
    linear_combination (-s) * Complex.I_sq
  rw [hn, hd, div_div_div_cancel_right₀ hden]
  rw [mul_div_mul_comm, div_eq_mul_inv (c + s * I), hinv]
  ring

/-- The translation `g_τ` in the Cayley picture: `C(g_τ ξ) = T_{C τ}(λ_τ C ξ)`, `λ_τ = -(τ - i)/(τ̄ + i)`. -/
theorem s19r4_trans (τ ξ : ℍ) (hτ : (τ : ℂ) ≠ I) (hξ : (ξ : ℂ) ≠ I) :
    (((s19rIwasawa (τ, 0) • ξ : ℍ) : ℂ) + I) / (((s19rIwasawa (τ, 0) • ξ : ℍ) : ℂ) - I) =
      (((τ : ℂ) + I) / ((τ : ℂ) - I) * (-((τ : ℂ) - I) / (conj (τ : ℂ) + I) * (((ξ : ℂ) + I) / ((ξ : ℂ) - I))) + 1) /
        (-((τ : ℂ) - I) / (conj (τ : ℂ) + I) * (((ξ : ℂ) + I) / ((ξ : ℂ) - I)) +
          conj (((τ : ℂ) + I) / ((τ : ℂ) - I))) := by
  obtain ⟨e00, e01, e10, e11⟩ := s19r4_iw_entries (τ, 0)
  simp only [Real.cos_zero, Real.sin_zero, mul_one, mul_zero, add_zero, neg_zero, zero_add] at e00 e01 e10 e11
  have hy := τ.im_pos
  have hs : 0 < √τ.im := Real.sqrt_pos.mpr hy
  have hsC : ((√τ.im : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  have hs2C : ((√τ.im : ℝ) : ℂ) ^ 2 = (τ.im : ℂ) := by exact_mod_cast Real.sq_sqrt hy.le
  have hP : ((s19rIwasawa (τ, 0) • ξ : ℍ) : ℂ) = (τ.im : ℂ) * ξ + τ.re := by
    rw [s19r4_act, e00, e01, e10, e11, ← hs2C]
    push_cast
    field_simp
    ring
  rw [hP]
  have hτc : (τ : ℂ) = (τ.re : ℂ) + (τ.im : ℂ) * I := (Complex.re_add_im _).symm
  have hconj : conj (τ : ℂ) = (τ.re : ℂ) - (τ.im : ℂ) * I := by
    rw [hτc, map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hcz : conj (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (conj (τ : ℂ) - I) / (conj (τ : ℂ) + I) := by
    rw [map_div₀, map_add, map_sub, Complex.conj_I]
    ring
  rw [hcz, hconj, hτc]
  have h1 : (τ.re : ℂ) + (τ.im : ℂ) * I - I ≠ 0 := by rw [← hτc]; exact sub_ne_zero.mpr hτ
  have h2 : (τ.re : ℂ) - (τ.im : ℂ) * I + I ≠ 0 := by
    intro h0
    apply h1
    have := congrArg conj h0
    rw [map_add, map_sub, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I, map_zero] at this
    linear_combination this
  have h3 : (ξ : ℂ) - I ≠ 0 := sub_ne_zero.mpr hξ
  set x : ℂ := (τ.re : ℂ)
  set y : ℂ := (τ.im : ℂ)
  set κ : ℂ := -2 * I / ((x - y * I + I) * ((ξ : ℂ) - I)) with hκ
  have hκ0 : κ ≠ 0 := by
    rw [hκ]
    exact div_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) (mul_ne_zero h2 h3)
  have hN : (x + y * I + I) / (x + y * I - I) * (-(x + y * I - I) / (x - y * I + I) * (((ξ : ℂ) + I) / ((ξ : ℂ) - I))) + 1 =
      κ * (y * ξ + x + I) := by
    rw [hκ]
    field_simp
    ring
  have hD : -(x + y * I - I) / (x - y * I + I) * (((ξ : ℂ) + I) / ((ξ : ℂ) - I)) + (x - y * I - I) / (x - y * I + I) =
      κ * (y * ξ + x - I) := by
    rw [hκ]
    field_simp
    ring
  rw [hN, hD, mul_div_mul_left _ _ hκ0]

/-- The sphere point: `C((g_τ k_θ a⁻¹) • i) = T_{C τ}(e^{i(arg λ_τ + 2θ)}/u)`. -/
theorem s19r4_sphere_pt (τ : ℍ) (hτ : (τ : ℂ) ≠ I) (θ : ℝ) {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    ((((s19rIwasawa (τ, θ) * (mautnerDiag (√((1 - u) / (1 + u))))⁻¹) • UpperHalfPlane.I : ℍ) : ℂ) + I) /
        ((((s19rIwasawa (τ, θ) * (mautnerDiag (√((1 - u) / (1 + u))))⁻¹) • UpperHalfPlane.I : ℍ) : ℂ) - I) =
      (((τ : ℂ) + I) / ((τ : ℂ) - I) *
          (exp (((Complex.arg (-((τ : ℂ) - I) / (conj (τ : ℂ) + I)) + 2 * θ : ℝ) : ℂ) * I) / u) + 1) /
        (exp (((Complex.arg (-((τ : ℂ) - I) / (conj (τ : ℂ) + I)) + 2 * θ : ℝ) : ℂ) * I) / u +
          conj (((τ : ℂ) + I) / ((τ : ℂ) - I))) := by
  have hu0 : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.1.ne'
  rw [mul_smul, s19r4_iw_split, mul_smul]
  set w : ℍ := (mautnerDiag (√((1 - u) / (1 + u))))⁻¹ • UpperHalfPlane.I with hwdef
  have hw : (w : ℂ) = I * (((1 + u) / (1 - u) : ℝ) : ℂ) := s19r4_inv_diag hu
  have h1u : (1 : ℂ) - u ≠ 0 := by exact_mod_cast (show (1 : ℝ) - u ≠ 0 by linarith [hu.2])
  have h1u' : (1 : ℂ) + u ≠ 0 := by exact_mod_cast (show (1 : ℝ) + u ≠ 0 by linarith [hu.1])
  have hwI : (w : ℂ) ≠ I := by
    rw [hw]
    intro h0
    have h1 : (((1 + u) / (1 - u) : ℝ) : ℂ) = 1 :=
      mul_left_cancel₀ Complex.I_ne_zero (h0.trans (mul_one I).symm)
    have h2 : (1 + u) / (1 - u) = (1 : ℝ) := by exact_mod_cast h1
    rw [div_eq_one_iff_eq (by linarith [hu.2])] at h2
    linarith [hu.1]
  have hCw : ((w : ℂ) + I) / ((w : ℂ) - I) = 1 / u := by
    rw [hw, show I * (((1 + u) / (1 - u) : ℝ) : ℂ) + I = I * ((((1 + u) / (1 - u) : ℝ) : ℂ) + 1) by ring,
      show I * (((1 + u) / (1 - u) : ℝ) : ℂ) - I = I * ((((1 + u) / (1 - u) : ℝ) : ℂ) - 1) by ring,
      mul_div_mul_left _ _ Complex.I_ne_zero]
    have htm1 : (((1 + u) / (1 - u) : ℝ) : ℂ) - 1 ≠ 0 := by
      have : (1 + u) / (1 - u) - 1 ≠ (0 : ℝ) := by
        rw [div_sub_one (by linarith [hu.2])]
        exact div_ne_zero (by linarith [hu.1]) (by linarith [hu.2])
      exact_mod_cast this
    rw [div_eq_div_iff htm1 hu0]
    push_cast
    field_simp
    ring
  set k : ℍ := s19rIwasawa (UpperHalfPlane.I, θ) • w with hkdef
  have hk := s19r4_rot θ w hwI
  rw [← hkdef, hCw] at hk
  have hcs := Real.sin_sq_add_cos_sq θ
  have hcsC : ((Real.sin θ : ℝ) : ℂ) ^ 2 + ((Real.cos θ : ℝ) : ℂ) ^ 2 = 1 := by exact_mod_cast hcs
  have hcc : ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I) * ((Real.cos θ : ℂ) - (Real.sin θ : ℂ) * I) = 1 := by
    linear_combination hcsC - ((Real.sin θ : ℝ) : ℂ) ^ 2 * Complex.I_sq
  have hcsn : ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I) ≠ 0 := left_ne_zero_of_mul_eq_one hcc
  have hkI : (k : ℂ) ≠ I := by
    intro h0
    rw [h0, sub_self, div_zero] at hk
    exact (mul_ne_zero (pow_ne_zero 2 hcsn) (one_div_ne_zero hu0)) hk.symm
  rw [s19r4_trans τ k hτ hkI, hk]
  -- the multiplier
  set lam : ℂ := -((τ : ℂ) - I) / (conj (τ : ℂ) + I) with hlam
  have hτI : (τ : ℂ) - I ≠ 0 := sub_ne_zero.mpr hτ
  have hlam1 : ‖lam‖ = 1 := by
    have : conj (τ : ℂ) + I = conj ((τ : ℂ) - I) := by rw [map_sub, Complex.conj_I]; ring
    rw [hlam, this, norm_div, norm_neg, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr hτI)]
  have hlame : lam = exp ((Complex.arg lam : ℂ) * I) := by
    have := Complex.norm_mul_exp_arg_mul_I lam
    rw [hlam1, Complex.ofReal_one, one_mul] at this
    exact this.symm
  have hrot : ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I) = exp ((θ : ℂ) * I) := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hmult : lam * (((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I) ^ 2 * (1 / u)) =
      exp (((Complex.arg lam + 2 * θ : ℝ) : ℂ) * I) / u := by
    rw [hrot]
    conv_lhs => rw [hlame]
    rw [sq, ← Complex.exp_add, ← mul_assoc, ← Complex.exp_add, mul_one_div]
    congr 2
    push_cast
    ring
  rw [hmult]

/-- `∫_0^π H(α + 2θ) dθ = ½ ∫_0^{2π} H` for `2π`-periodic `H`. -/
theorem s19r4_theta {H : ℝ → ℝ} (hper : Function.Periodic H (2 * π)) (α : ℝ) :
    (∫ θ in Ico 0 π, H (α + 2 * θ)) = 1 / 2 * ∫ θ in (0 : ℝ)..2 * π, H θ := by
  rw [integral_Ico_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le Real.pi_pos.le,
    intervalIntegral.integral_comp_add_mul H (two_ne_zero) α, mul_zero, add_zero,
    hper.intervalIntegral_add_eq α 0, zero_add, smul_eq_mul]
  ring

/-- The Iwasawa map is measurable. -/
theorem s19r4_iw_meas : Measurable s19rIwasawa := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℝ))
  haveI : SecondCountableTopology SL(2, ℝ) :=
    (Matrix.SpecialLinearGroup.isClosedEmbedding_val (n := Fin 2) (R := ℝ)).isInducing.secondCountableTopology
  have him : Measurable fun p : ℍ × ℝ => p.1.im :=
    (Complex.measurable_im.comp UpperHalfPlane.measurable_coe).comp measurable_fst
  have hre : Measurable fun p : ℍ × ℝ => p.1.re :=
    (Complex.measurable_re.comp UpperHalfPlane.measurable_coe).comp measurable_fst
  have hsq : Measurable fun p : ℍ × ℝ => √p.1.im := Real.continuous_sqrt.measurable.comp him
  have hc : Measurable fun p : ℍ × ℝ => Real.cos p.2 := Real.continuous_cos.measurable.comp measurable_snd
  have hs : Measurable fun p : ℍ × ℝ => Real.sin p.2 := Real.continuous_sin.measurable.comp measurable_snd
  unfold s19rIwasawa
  refine Measurable.mul ?_ ?_
  · refine Measurable.subtype_mk ?_
    refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
    fin_cases i <;> fin_cases j
    · exact hsq
    · exact hre.div hsq
    · exact measurable_const
    · exact measurable_const.div hsq
  · refine Measurable.subtype_mk ?_
    refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
    fin_cases i <;> fin_cases j
    · exact hc
    · exact hs.neg
    · exact hs
    · exact hc

/-- The orbit map `x ↦ x • i` is measurable (as a `ℂ`-valued map). -/
theorem s19r4_orbit_meas : Measurable fun x : SL(2, ℝ) => ((x • UpperHalfPlane.I : ℍ) : ℂ) := by
  have he : (fun x : SL(2, ℝ) => ((x • UpperHalfPlane.I : ℍ) : ℂ)) =
      fun x => ((x 0 0 : ℂ) * I + x 0 1) / ((x 1 0 : ℂ) * I + x 1 1) := by
    funext x
    rw [s19r4_act, UpperHalfPlane.coe_I]
  have hij : ∀ i j : Fin 2, Measurable fun x : SL(2, ℝ) => ((x i j : ℝ) : ℂ) := fun i j =>
    Complex.measurable_ofReal.comp ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_subtype_coe))
  rw [he]
  exact (((hij 0 0).mul_const I).add (hij 0 1)).div (((hij 1 0).mul_const I).add (hij 1 1))

/-- `μ(D) < ∞`. -/
theorem s19r4_muD {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {Γ' : Subgroup SL(2, ℝ)} (hΓ' : LiZhongQC.IsFuchsian Γ')
    (hneg : -1 ∈ Γ')
    (hrel : ∀ M ∈ Γ', ∃ g ∈ Γ, ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I))
    (hrel' : ∀ g ∈ Γ, ∃ M ∈ Γ', ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I)) :
    s19rMeasure (s19rDomain Γ) < ⊤ := by
  obtain ⟨-, -, -, hint⟩ := s19r_domain hΓ hΓ' hneg hrel hrel'
  have h := hint (fun _ => 1) measurable_const
  simp only [one_mul] at h
  rw [setLIntegral_one] at h
  rw [h]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hΓ.2

/-- Integrals over `D` in Iwasawa coordinates: `∫_D F dμ = ∫_{C τ ∈ F} ∫_0^π F(g_τ k_θ) dθ dvol(τ)`. -/
theorem s19r4_coords {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {Γ' : Subgroup SL(2, ℝ)}
    (hΓ' : LiZhongQC.IsFuchsian Γ') (hneg : -1 ∈ Γ')
    (hrel : ∀ M ∈ Γ', ∃ g ∈ Γ, ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I))
    (hrel' : ∀ g ∈ Γ, ∃ M ∈ Γ', ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I))
    {Fb : SL(2, ℝ) → ℝ} (hFm : Measurable Fb) {C : ℝ} (hFb : ∀ x, |Fb x| ≤ C) :
    (∫ x in s19rDomain Γ, Fb x ∂s19rMeasure) =
      ∫ τ : ℍ, {τ : ℍ | ((τ : ℂ) + I) / ((τ : ℂ) - I) ∈ fundDomain Γ}.indicator
        (fun τ => ∫ θ in Ico 0 π, Fb (s19rIwasawa (τ, θ))) τ := by
  obtain ⟨hDm, -, -, -⟩ := s19r_domain hΓ hΓ' hneg hrel hrel'
  have hμD := s19r4_muD hΓ hΓ' hneg hrel hrel'
  haveI : IsFiniteMeasure (s19rMeasure.restrict (s19rDomain Γ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hμD⟩
  have hIw := s19r4_iw_meas
  have hInt : Integrable ((s19rDomain Γ).indicator Fb) s19rMeasure := by
    refine (integrable_indicator_iff hDm).mpr ?_
    refine Integrable.mono' (integrable_const C) hFm.aestronglyMeasurable ?_
    exact Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hFb x
  rw [← integral_indicator hDm]
  rw [show s19rMeasure = Measure.map s19rIwasawa ((volume : Measure ℍ).prod (volume.restrict (Ico 0 (2 * π))))
    from rfl] at hInt ⊢
  have hInt' := (integrable_map_measure (hFm.indicator hDm).aestronglyMeasurable hIw.aemeasurable).mp hInt
  have hInt'' : Integrable (fun p => (s19rDomain Γ).indicator Fb (s19rIwasawa p))
      ((volume : Measure ℍ).prod (volume.restrict (Ico 0 (2 * π)))) := hInt'
  rw [integral_map hIw.aemeasurable (hFm.indicator hDm).aestronglyMeasurable, integral_prod _ hInt'']
  refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
  simp only [Function.comp]
  by_cases hτ : ((τ : ℂ) + I) / ((τ : ℂ) - I) ∈ fundDomain Γ
  · rw [indicator_of_mem (show τ ∈ {τ : ℍ | ((τ : ℂ) + I) / ((τ : ℂ) - I) ∈ fundDomain Γ} from hτ)]
    calc (∫ θ in Ico 0 (2 * π), (s19rDomain Γ).indicator Fb (s19rIwasawa (τ, θ))) =
        ∫ θ in Ico 0 (2 * π), (Ico 0 π).indicator (fun θ => Fb (s19rIwasawa (τ, θ))) θ := by
          refine setIntegral_congr_fun measurableSet_Ico fun θ hθ => ?_
          by_cases hθπ : θ < π
          · rw [indicator_of_mem ((s19r4_iw_mem (Γ := Γ) τ hθ).mpr ⟨hτ, hθπ⟩),
              indicator_of_mem (show θ ∈ Ico 0 π from ⟨hθ.1, hθπ⟩)]
          · rw [indicator_of_notMem (fun h => hθπ ((s19r4_iw_mem (Γ := Γ) τ hθ).mp h).2),
              indicator_of_notMem (fun h => hθπ h.2)]
      _ = ∫ θ in Ico 0 (2 * π) ∩ Ico 0 π, Fb (s19rIwasawa (τ, θ)) := setIntegral_indicator measurableSet_Ico
      _ = _ := by rw [inter_eq_right.mpr (Ico_subset_Ico_right (by linarith [Real.pi_pos]))]
  · rw [indicator_of_notMem (show τ ∉ {τ : ℍ | ((τ : ℂ) + I) / ((τ : ℂ) - I) ∈ fundDomain Γ} from hτ)]
    exact setIntegral_eq_zero_of_forall_eq_zero fun θ hθ =>
      indicator_of_notMem (fun h => hτ ((s19r4_iw_mem (Γ := Γ) τ hθ).mp h).1) _

/-- R2's orbit formula for bounded real functions: `∫_D G(C(g•i)) dμ = π ∬_F G ρ`. -/
theorem s19r4_dom_bochner {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {Γ' : Subgroup SL(2, ℝ)}
    (hΓ' : LiZhongQC.IsFuchsian Γ') (hneg : -1 ∈ Γ')
    (hrel : ∀ M ∈ Γ', ∃ g ∈ Γ, ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I))
    (hrel' : ∀ g ∈ Γ, ∃ M ∈ Γ', ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I))
    {G : ℂ → ℝ} (hGm : Measurable G) {C : ℝ} (hGb : ∀ z, |G z| ≤ C) :
    (∫ x in s19rDomain Γ, G ((((x • UpperHalfPlane.I : ℍ) : ℂ) + I) / (((x • UpperHalfPlane.I : ℍ) : ℂ) - I))
        ∂s19rMeasure) = π * ∫ z in fundDomain Γ, G z * rho z := by
  obtain ⟨hDm, -, -, hint⟩ := s19r_domain hΓ hΓ' hneg hrel hrel'
  have hμD := s19r4_muD hΓ hΓ' hneg hrel hrel'
  haveI : IsFiniteMeasure (s19rMeasure.restrict (s19rDomain Γ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hμD⟩
  have hom := s19r4_orbit_meas
  have hm : Measurable fun x : SL(2, ℝ) =>
      G ((((x • UpperHalfPlane.I : ℍ) : ℂ) + I) / (((x • UpperHalfPlane.I : ℍ) : ℂ) - I)) :=
    hGm.comp ((hom.add_const I).div (hom.sub_const I))
  have hi1 : Integrable (fun x : SL(2, ℝ) =>
      G ((((x • UpperHalfPlane.I : ℍ) : ℂ) + I) / (((x • UpperHalfPlane.I : ℍ) : ℂ) - I)))
      (s19rMeasure.restrict (s19rDomain Γ)) :=
    Integrable.mono' (integrable_const C) hm.aestronglyMeasurable
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hGb _)
  have hi2 : IntegrableOn (fun z => G z * rho z) (fundDomain Γ) := s19c_bdd_F hΓ hGm (fun z _ => hGb z)
  have hρ0 : ∀ z, 0 ≤ rho z := fun z => div_nonneg (by norm_num) (sq_nonneg _)
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi1,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi2]
  have h1 := hint (fun z => ENNReal.ofReal (G z)) (ENNReal.measurable_ofReal.comp hGm)
  have h2 := hint (fun z => ENNReal.ofReal (-G z)) (ENNReal.measurable_ofReal.comp hGm.neg)
  rw [h1, h2]
  have e1 : (∫⁻ z in fundDomain Γ, ENNReal.ofReal (G z * rho z)) =
      ∫⁻ z in fundDomain Γ, ENNReal.ofReal (G z) * ENNReal.ofReal (rho z) :=
    lintegral_congr fun z => ENNReal.ofReal_mul' (hρ0 z)
  have e2 : (∫⁻ z in fundDomain Γ, ENNReal.ofReal (-(G z * rho z))) =
      ∫⁻ z in fundDomain Γ, ENNReal.ofReal (-G z) * ENNReal.ofReal (rho z) :=
    lintegral_congr fun z => by rw [← neg_mul, ENNReal.ofReal_mul' (hρ0 z)]
  rw [e1, e2, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal Real.pi_pos.le]
  ring

/-- The Cayley map sends `ℍ` into `𝔻*`, except the junk value `0` at `i`. -/
theorem s19r4_cayley_mem (ξ : ℍ) :
    ((ξ : ℂ) + I) / ((ξ : ℂ) - I) ∈ unitDiscExterior ∨ ((ξ : ℂ) + I) / ((ξ : ℂ) - I) = 0 := by
  by_cases hξ : (ξ : ℂ) = I
  · right
    rw [hξ, sub_self, div_zero]
  · left
    have hd : 0 < ‖(ξ : ℂ) - I‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hξ)
    show 1 < ‖((ξ : ℂ) + I) / ((ξ : ℂ) - I)‖
    rw [norm_div, one_lt_div hd]
    have hy := ξ.im_pos
    have hsq : ‖(ξ : ℂ) - I‖ ^ 2 < ‖(ξ : ℂ) + I‖ ^ 2 := by
      simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
        Complex.sub_im, Complex.I_re, Complex.I_im, UpperHalfPlane.coe_im]
      nlinarith
    nlinarith [norm_nonneg ((ξ : ℂ) + I)]

/-- The inner `θ`-integral of the R4 (S) integrand over a Iwasawa fibre: `g(z) · ½ Ψ(z)` with `z = C τ`. -/
theorem s19r4_inner (τ : ℍ) (hτI : (τ : ℂ) ≠ I) (f g : ℂ → ℝ) {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    (∫ θ in Ico 0 π, g ((((s19rIwasawa (τ, θ) • UpperHalfPlane.I : ℍ) : ℂ) + I) /
        (((s19rIwasawa (τ, θ) • UpperHalfPlane.I : ℍ) : ℂ) - I)) *
      f (((((s19rIwasawa (τ, θ) * (mautnerDiag (√((1 - u) / (1 + u))))⁻¹) • UpperHalfPlane.I : ℍ) : ℂ) + I) /
        ((((s19rIwasawa (τ, θ) * (mautnerDiag (√((1 - u) / (1 + u))))⁻¹) • UpperHalfPlane.I : ℍ) : ℂ) - I))) =
      g (((τ : ℂ) + I) / ((τ : ℂ) - I)) * (1 / 2 * ∫ θ in (0 : ℝ)..2 * π,
        f ((((τ : ℂ) + I) / ((τ : ℂ) - I) * (exp (θ * I) / u) + 1) /
          (exp (θ * I) / u + conj (((τ : ℂ) + I) / ((τ : ℂ) - I))))) := by
  set z := ((τ : ℂ) + I) / ((τ : ℂ) - I) with hzdef
  set α := Complex.arg (-((τ : ℂ) - I) / (conj (τ : ℂ) + I))
  set H : ℝ → ℝ := fun φ => f ((z * (exp ((φ : ℂ) * I) / u) + 1) / (exp ((φ : ℂ) * I) / u + conj z)) with hHdef
  have hper : Function.Periodic H (2 * π) := fun φ => by
    simp only [hHdef]
    rw [show ((φ + 2 * π : ℝ) : ℂ) * I = (φ : ℂ) * I + 2 * π * I by push_cast; ring, Complex.exp_add,
      Complex.exp_two_pi_mul_I, mul_one]
  have hpt : ∀ θ : ℝ, g ((((s19rIwasawa (τ, θ) • UpperHalfPlane.I : ℍ) : ℂ) + I) /
        (((s19rIwasawa (τ, θ) • UpperHalfPlane.I : ℍ) : ℂ) - I)) *
      f (((((s19rIwasawa (τ, θ) * (mautnerDiag (√((1 - u) / (1 + u))))⁻¹) • UpperHalfPlane.I : ℍ) : ℂ) + I) /
        ((((s19rIwasawa (τ, θ) * (mautnerDiag (√((1 - u) / (1 + u))))⁻¹) • UpperHalfPlane.I : ℍ) : ℂ) - I)) = g z * H (α + 2 * θ) := fun θ => by
    rw [s19r4_iw_act, s19r4_sphere_pt τ hτI θ hu]
  simp only [hpt]
  rw [integral_const_mul, s19r4_theta hper α]

/-- `∫_ℍ 1_{F'}(τ) G(C τ) dvol = ∬_F G ρ` for bounded measurable `G`, via `s19r4_coords` and R2. -/
theorem s19r4_transfer {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {Γ' : Subgroup SL(2, ℝ)}
    (hΓ' : LiZhongQC.IsFuchsian Γ') (hneg : -1 ∈ Γ')
    (hrel : ∀ M ∈ Γ', ∃ g ∈ Γ, ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I))
    (hrel' : ∀ g ∈ Γ, ∃ M ∈ Γ', ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I))
    {G : ℂ → ℝ} (hGm : Measurable G) {C : ℝ} (hGb : ∀ z, |G z| ≤ C) :
    (∫ τ : ℍ, {τ : ℍ | ((τ : ℂ) + I) / ((τ : ℂ) - I) ∈ fundDomain Γ}.indicator
        (fun τ => G (((τ : ℂ) + I) / ((τ : ℂ) - I))) τ) = ∫ z in fundDomain Γ, G z * rho z := by
  have hom := s19r4_orbit_meas
  have hGCm : Measurable fun x : SL(2, ℝ) =>
      G ((((x • UpperHalfPlane.I : ℍ) : ℂ) + I) / (((x • UpperHalfPlane.I : ℍ) : ℂ) - I)) :=
    hGm.comp ((hom.add_const I).div (hom.sub_const I))
  have hc1 := s19r4_coords hΓ hΓ' hneg hrel hrel' hGCm (fun x => hGb _)
  have hc2 := s19r4_dom_bochner hΓ hΓ' hneg hrel hrel' hGm hGb
  rw [hc2] at hc1
  have hconst : ∀ τ : ℍ, (∫ θ in Ico 0 π, G ((((s19rIwasawa (τ, θ) • UpperHalfPlane.I : ℍ) : ℂ) + I) /
      (((s19rIwasawa (τ, θ) • UpperHalfPlane.I : ℍ) : ℂ) - I))) = π * G (((τ : ℂ) + I) / ((τ : ℂ) - I)) := by
    intro τ
    simp only [s19r4_iw_act]
    rw [setIntegral_const, Real.volume_real_Ico_of_le Real.pi_pos.le, sub_zero, smul_eq_mul]
  simp only [hconst] at hc1
  have hind : ∀ τ : ℍ, {τ : ℍ | ((τ : ℂ) + I) / ((τ : ℂ) - I) ∈ fundDomain Γ}.indicator
      (fun τ => π * G (((τ : ℂ) + I) / ((τ : ℂ) - I))) τ =
      π * {τ : ℍ | ((τ : ℂ) + I) / ((τ : ℂ) - I) ∈ fundDomain Γ}.indicator
        (fun τ => G (((τ : ℂ) + I) / ((τ : ℂ) - I))) τ := fun τ => by
    by_cases hτ : τ ∈ {τ : ℍ | ((τ : ℂ) + I) / ((τ : ℂ) - I) ∈ fundDomain Γ}
    · rw [indicator_of_mem hτ, indicator_of_mem hτ]
    · rw [indicator_of_notMem hτ, indicator_of_notMem hτ, mul_zero]
  simp only [hind, integral_const_mul] at hc1
  exact (mul_left_cancel₀ Real.pi_pos.ne' hc1).symm

/-- The R4 (S) integrand on `SL(2, ℝ)` is measurable and bounded. -/
theorem s19r4_integrand {f g : ℂ → ℝ} (hfm : Measurable f) (hgm : Measurable g) {Cf Cg : ℝ}
    (hCf : ∀ z ∈ unitDiscExterior, |f z| ≤ Cf) (hCg : ∀ z ∈ unitDiscExterior, |g z| ≤ Cg) (u : ℝ) :
    Measurable (fun x : SL(2, ℝ) => g ((((x • UpperHalfPlane.I : ℍ) : ℂ) + I) / (((x • UpperHalfPlane.I : ℍ) : ℂ) - I)) * f (((((x * (mautnerDiag (√((1 - u) / (1 + u))))⁻¹) • UpperHalfPlane.I : ℍ) : ℂ) + I) / ((((x * (mautnerDiag (√((1 - u) / (1 + u))))⁻¹) • UpperHalfPlane.I : ℍ) : ℂ) - I))) ∧
      ∀ x : SL(2, ℝ), |g ((((x • UpperHalfPlane.I : ℍ) : ℂ) + I) / (((x • UpperHalfPlane.I : ℍ) : ℂ) - I)) * f (((((x * (mautnerDiag (√((1 - u) / (1 + u))))⁻¹) • UpperHalfPlane.I : ℍ) : ℂ) + I) / ((((x * (mautnerDiag (√((1 - u) / (1 + u))))⁻¹) • UpperHalfPlane.I : ℍ) : ℂ) - I))| ≤ max Cg |g 0| * max Cf |f 0| := by
  have hfB : ∀ ξ : ℍ, |f (((ξ : ℂ) + I) / ((ξ : ℂ) - I))| ≤ max Cf |f 0| := fun ξ => by
    rcases s19r4_cayley_mem ξ with h | h
    · exact (hCf _ h).trans (le_max_left _ _)
    · rw [h]; exact le_max_right _ _
  have hgB : ∀ ξ : ℍ, |g (((ξ : ℂ) + I) / ((ξ : ℂ) - I))| ≤ max Cg |g 0| := fun ξ => by
    rcases s19r4_cayley_mem ξ with h | h
    · exact (hCg _ h).trans (le_max_left _ _)
    · rw [h]; exact le_max_right _ _
  have hCg0 : 0 ≤ max Cg |g 0| := (abs_nonneg _).trans (le_max_right _ _)
  have hom := s19r4_orbit_meas
  have hom2 : Measurable fun x : SL(2, ℝ) => (((x * (mautnerDiag (√((1 - u) / (1 + u))))⁻¹) • UpperHalfPlane.I : ℍ) : ℂ) := by
    haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℝ) :=
      inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℝ))
    haveI : SecondCountableTopology SL(2, ℝ) :=
      (Matrix.SpecialLinearGroup.isClosedEmbedding_val (n := Fin 2) (R := ℝ)).isInducing.secondCountableTopology
    exact hom.comp (measurable_mul_const _)
  refine ⟨(hgm.comp ((hom.add_const I).div (hom.sub_const I))).mul
    (hfm.comp ((hom2.add_const I).div (hom2.sub_const I))), fun x => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hgB _) (hfB _) (abs_nonneg _) hCg0

/-- The half-weight `G = 1_{𝔻*} · g · ½Ψ` of R4 (S) is measurable and bounded. -/
theorem s19r4_Gbound {f g : ℂ → ℝ} (hfm : Measurable f) (hgm : Measurable g) {Cf Cg : ℝ}
    (hCf : ∀ z ∈ unitDiscExterior, |f z| ≤ Cf) (hCg : ∀ z ∈ unitDiscExterior, |g z| ≤ Cg)
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    Measurable (fun z => unitDiscExterior.indicator (fun z => g z * (1 / 2 * ∫ θ in (0 : ℝ)..2 * π, f ((z * (exp (θ * I) / u) + 1) / (exp (θ * I) / u + conj z)))) z) ∧ ∀ z, |unitDiscExterior.indicator (fun z => g z * (1 / 2 * ∫ θ in (0 : ℝ)..2 * π, f ((z * (exp (θ * I) / u) + 1) / (exp (θ * I) / u + conj z)))) z| ≤ max Cg |g 0| * (π * max Cf |f 0|) := by
  have hCf0 : 0 ≤ max Cf |f 0| := (abs_nonneg _).trans (le_max_right _ _)
  have hCg0 : 0 ≤ max Cg |g 0| := (abs_nonneg _).trans (le_max_right _ _)
  obtain ⟨hΨm2, hΨb⟩ := s19c_Psi hfm hCf
  have hΨm : Measurable fun z => ∫ θ in (0 : ℝ)..2 * π, f ((z * (exp (θ * I) / u) + 1) / (exp (θ * I) / u + conj z)) := by
    have h := hΨm2.comp (show Measurable fun z : ℂ => (z, u) from measurable_id.prodMk measurable_const)
    exact h
  have hext : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  refine ⟨(hgm.mul (measurable_const.mul hΨm)).indicator hext, fun z => ?_⟩
  by_cases hz : z ∈ unitDiscExterior
  · rw [indicator_of_mem hz, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have h1 := hΨb z hz u hu
    have h2 : |g z| ≤ max Cg |g 0| := (hCg z hz).trans (le_max_left _ _)
    calc |g z| * (1 / 2 * |∫ θ in (0 : ℝ)..2 * π, f ((z * (exp (θ * I) / u) + 1) / (exp (θ * I) / u + conj z))|) ≤ max Cg |g 0| * (1 / 2 * (2 * π * max Cf |f 0|)) := by
          exact mul_le_mul h2 (mul_le_mul_of_nonneg_left h1 (by norm_num)) (by positivity) hCg0
    _ = max Cg |g 0| * (π * max Cf |f 0|) := by ring
  · rw [indicator_of_notMem hz, abs_zero]
    exact mul_nonneg hCg0 (mul_nonneg Real.pi_pos.le hCf0)

/-- The scalar identity closing R4 (S). -/
theorem s19r4_alg (a b c : ℝ) : b * (1 / 2 * a) * c = π * (a / (2 * π) * b * c) := by
  have hpi2 : π * (1 / (2 * π)) = 1 / 2 := by rw [mul_one_div, div_mul_cancel_right₀ Real.pi_pos.ne', one_div]
  rw [div_eq_mul_one_div a (2 * π)]
  linear_combination (-(a * b * c)) * hpi2

/-- **R4 (S).** The diagonal coefficient of the lifts is `π` times the sphere pairing. -/
theorem s19r4_sphere {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {Γ' : Subgroup SL(2, ℝ)}
    (hΓ' : LiZhongQC.IsFuchsian Γ') (hneg : -1 ∈ Γ')
    (hrel : ∀ M ∈ Γ', ∃ g ∈ Γ, ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I))
    (hrel' : ∀ g ∈ Γ, ∃ M ∈ Γ', ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I))
    {f g : ℂ → ℝ} (hfm : Measurable f) (hgm : Measurable g) {Cf Cg : ℝ}
    (hCf : ∀ z ∈ unitDiscExterior, |f z| ≤ Cf) (hCg : ∀ z ∈ unitDiscExterior, |g z| ≤ Cg)
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    (∫ x in s19rDomain Γ,
        g ((((x • UpperHalfPlane.I : ℍ) : ℂ) + I) / (((x • UpperHalfPlane.I : ℍ) : ℂ) - I)) *
          f (((((x * (mautnerDiag (√((1 - u) / (1 + u))))⁻¹) • UpperHalfPlane.I : ℍ) : ℂ) + I) /
            ((((x * (mautnerDiag (√((1 - u) / (1 + u))))⁻¹) • UpperHalfPlane.I : ℍ) : ℂ) - I)) ∂s19rMeasure) =
      π * ∫ z in fundDomain Γ, (∫ θ in (0 : ℝ)..2 * π,
        f ((z * (exp (θ * I) / u) + 1) / (exp (θ * I) / u + conj z))) / (2 * π) * g z * rho z := by
  have hFe := fundDomain_subset Γ
  obtain ⟨hFm, hFb⟩ := s19r4_integrand hfm hgm hCf hCg u
  rw [s19r4_coords hΓ hΓ' hneg hrel hrel' hFm hFb]
  obtain ⟨hGm, hGb⟩ := s19r4_Gbound hfm hgm hCf hCg hu
  rw [← integral_const_mul]
  refine (integral_congr_ae (Eventually.of_forall fun τ => ?_)).trans
    ((s19r4_transfer hΓ hΓ' hneg hrel hrel' hGm hGb).trans
      (setIntegral_congr_fun (fundDomain_measurable Γ) fun z hz => ?_))
  · by_cases hτ : ((τ : ℂ) + I) / ((τ : ℂ) - I) ∈ fundDomain Γ
    · have hτI : (τ : ℂ) ≠ I := by
        intro h0
        have : ((τ : ℂ) + I) / ((τ : ℂ) - I) = 0 := by rw [h0, sub_self, div_zero]
        rw [this] at hτ
        have h1 : (1 : ℝ) < ‖(0 : ℂ)‖ := hFe hτ
        rw [norm_zero] at h1
        linarith
      rw [indicator_of_mem (show τ ∈ {τ : ℍ | ((τ : ℂ) + I) / ((τ : ℂ) - I) ∈ fundDomain Γ} from hτ), indicator_of_mem (show τ ∈ {τ : ℍ | ((τ : ℂ) + I) / ((τ : ℂ) - I) ∈ fundDomain Γ} from hτ)]
      beta_reduce
      rw [s19r4_inner τ hτI f g hu, indicator_of_mem (hFe hτ)]
    · rw [indicator_of_notMem (show τ ∉ {τ : ℍ | ((τ : ℂ) + I) / ((τ : ℂ) - I) ∈ fundDomain Γ} from hτ), indicator_of_notMem (show τ ∉ {τ : ℍ | ((τ : ℂ) + I) / ((τ : ℂ) - I) ∈ fundDomain Γ} from hτ)]
  · beta_reduce
    rw [indicator_of_mem (hFe hz)]
    exact s19r4_alg _ _ _

/-- **R4.** (E) translation-invariant vectors of `L²(μ|_D)` are a.e. constant; (S) the diagonal coefficient
`a = (mautnerDiag √((1-u)/(1+u)))⁻¹` of the lifts is `π` times the sphere pairing at pseudo-radius `u`. -/
theorem s19r_erg_link {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {Γ' : Subgroup SL(2, ℝ)} (hΓ' : LiZhongQC.IsFuchsian Γ') (hneg : -1 ∈ Γ')
    (hrel : ∀ M ∈ Γ', ∃ g ∈ Γ, ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I))
    (hrel' : ∀ g ∈ Γ, ∃ M ∈ Γ', ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I)) :
    (∀ φ : SL(2, ℝ) → ℝ, MemLp φ 2 (s19rMeasure.restrict (s19rDomain Γ)) →
      (∀ h : SL(2, ℝ), (fun g => ∑' γ : Γ', (s19rDomain Γ).indicator φ ((γ : SL(2, ℝ)) * g * h))
        =ᵐ[s19rMeasure.restrict (s19rDomain Γ)] φ) →
      ∃ c : ℝ, φ =ᵐ[s19rMeasure.restrict (s19rDomain Γ)] fun _ => c) ∧
    ∀ f g : ℂ → ℝ, Measurable f → Measurable g →
      (∃ C, ∀ z ∈ unitDiscExterior, |f z| ≤ C) → (∃ C, ∀ z ∈ unitDiscExterior, |g z| ≤ C) →
      (∀ γ ∈ Γ, ∀ z ∈ unitDiscExterior, f (mob γ z) = f z) →
      (∀ γ ∈ Γ, ∀ z ∈ unitDiscExterior, g (mob γ z) = g z) →
      ∀ u ∈ Ioo (0 : ℝ) 1,
        (∫ x in s19rDomain Γ,
            g ((((x • UpperHalfPlane.I : ℍ) : ℂ) + I) / (((x • UpperHalfPlane.I : ℍ) : ℂ) - I)) *
              f (((((x * (mautnerDiag (√((1 - u) / (1 + u))))⁻¹) • UpperHalfPlane.I : ℍ) : ℂ) + I) /
                ((((x * (mautnerDiag (√((1 - u) / (1 + u))))⁻¹) • UpperHalfPlane.I : ℍ) : ℂ) - I)) ∂s19rMeasure) =
          π * ∫ z in fundDomain Γ, (∫ θ in (0 : ℝ)..2 * π,
            f ((z * (exp (θ * I) / u) + 1) / (exp (θ * I) / u + conj z))) / (2 * π) * g z * rho z := by
  refine ⟨fun φ hφ hfix => s19r4_erg hΓ hΓ' hneg hrel hrel' hφ hfix, ?_⟩
  -- (S) holds for any bounded measurable `f`, `g`; the automorphy hypotheses are not needed for it.
  intro f g hfm hgm hfb hgb _ _ u hu
  obtain ⟨Cf, hCf⟩ := hfb
  obtain ⟨Cg, hCg⟩ := hgb
  exact s19r4_sphere hΓ hΓ' hneg hrel hrel' hfm hgm hCf hCg hu

/-! ### Final assembly: the packaged representation `hrep` and Lemma 1.9 (`s19f` prefix) -/

/-- **F1.** Enlarging `Γ'` to `Γ' ⊔ {±1}` keeps it Fuchsian and keeps the Cayley relations with `Γ`. -/
theorem s19f_enlarge {Γ : Subgroup SL2C} {Γ' : Subgroup SL(2, ℝ)} (hΓ' : LiZhongQC.IsFuchsian Γ')
    (hrel : ∀ M ∈ Γ', ∃ g ∈ Γ, ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I))
    (hrel' : ∀ g ∈ Γ, ∃ M ∈ Γ', ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I)) :
    ∃ Γ'' : Subgroup SL(2, ℝ), LiZhongQC.IsFuchsian Γ'' ∧ -1 ∈ Γ'' ∧
      (∀ M ∈ Γ'', ∃ g ∈ Γ, ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
        mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I)) ∧
      ∀ g ∈ Γ, ∃ M ∈ Γ'', ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
        mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I) := by
  have hnsm : ∀ (M : SL(2, ℝ)) (τ : ℍ), (-M) • τ = M • τ := fun M τ => by
    apply UpperHalfPlane.ext
    rw [s19r4_act, s19r4_act]
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Complex.ofReal_neg, neg_mul, ← neg_add,
      neg_div_neg_eq]
  have hninv : ∀ a : SL(2, ℝ), (-a)⁻¹ = -a⁻¹ := fun a =>
    inv_eq_of_mul_eq_one_right (by rw [neg_mul_neg, mul_inv_cancel])
  refine ⟨{ carrier := {x | x ∈ Γ' ∨ -x ∈ Γ'}
            mul_mem' := ?_
            one_mem' := Or.inl Γ'.one_mem
            inv_mem' := ?_ }, ?_, ?_, ?_, ?_⟩
  · intro a b ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact Or.inl (Γ'.mul_mem ha hb)
    · exact Or.inr (by rw [← mul_neg]; exact Γ'.mul_mem ha hb)
    · exact Or.inr (by rw [← neg_mul]; exact Γ'.mul_mem ha hb)
    · exact Or.inl (by rw [← neg_mul_neg]; exact Γ'.mul_mem ha hb)
  · intro a ha
    rcases ha with ha | ha
    · exact Or.inl (Γ'.inv_mem ha)
    · exact Or.inr (by rw [← hninv]; exact Γ'.inv_mem ha)
  · intro K hK
    refine ((hΓ' K hK).union ((hΓ' K hK).image fun x => -x)).subset ?_
    intro γ hγ
    obtain ⟨hγm, hγK⟩ := hγ
    rcases hγm with hγm | hγm
    · exact Or.inl ⟨hγm, hγK⟩
    · refine Or.inr ⟨-γ, ⟨hγm, ?_⟩, neg_neg γ⟩
      obtain ⟨y, ⟨ξ, hξ, hξy⟩, hyK⟩ := hγK
      exact ⟨y, ⟨ξ, hξ, by show (-γ) • ξ = y; rw [hnsm]; exact hξy⟩, hyK⟩
  · show -1 ∈ Γ' ∨ -(-1) ∈ Γ'
    exact Or.inr (by rw [neg_neg]; exact Γ'.one_mem)
  · intro M hM
    rcases hM with hM | hM
    · exact hrel M hM
    · obtain ⟨g, hg, hgM⟩ := hrel (-M) hM
      refine ⟨g, hg, fun τ hτ hMτ => ?_⟩
      have := hgM τ hτ (by rw [hnsm]; exact hMτ)
      rw [hnsm] at this
      exact this
  · intro g hg
    obtain ⟨M, hM, hgM⟩ := hrel' g hg
    exact ⟨M, Or.inl hM, hgM⟩

/-- **F2.** A.e. on `D`, the fold sum has a single term: one `γ₀` with `γ₀ g h ∈ D`, and the sum is `φ(γ₀ g h)`. -/
theorem s19f_single {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {Γ' : Subgroup SL(2, ℝ)} (hΓ' : LiZhongQC.IsFuchsian Γ')
    (hneg : -1 ∈ Γ')
    (hrel : ∀ M ∈ Γ', ∃ g ∈ Γ, ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I))
    (hrel' : ∀ g ∈ Γ, ∃ M ∈ Γ', ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I))
    (h : SL(2, ℝ)) :
    ∀ᵐ g ∂(s19rMeasure.restrict (s19rDomain Γ)), ∃ γ₀ : Γ', (γ₀ : SL(2, ℝ)) * g * h ∈ s19rDomain Γ ∧
      ∀ φ : SL(2, ℝ) → ℝ, (∑' γ : Γ', (s19rDomain Γ).indicator φ ((γ : SL(2, ℝ)) * g * h)) =
        φ ((γ₀ : SL(2, ℝ)) * g * h) := by
  obtain ⟨-, -, huniq, -⟩ := s19r_domain hΓ hΓ' hneg hrel hrel'
  filter_upwards [huniq h] with g hg
  obtain ⟨γ₀, hγ₀, hu⟩ := hg
  refine ⟨γ₀, hγ₀, fun φ => ?_⟩
  rw [tsum_eq_single γ₀ (fun γ hγ => indicator_of_notMem (fun hm => hγ (hu γ hm)) _), indicator_of_mem hγ₀]

/-- **F3.** The fold respects a.e. equality of square-integrable functions. -/
theorem s19f_fold_congr {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {Γ' : Subgroup SL(2, ℝ)}
    (hΓ' : LiZhongQC.IsFuchsian Γ') (hneg : -1 ∈ Γ')
    (hrel : ∀ M ∈ Γ', ∃ g ∈ Γ, ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I))
    (hrel' : ∀ g ∈ Γ, ∃ M ∈ Γ', ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I))
    {φ ψ : SL(2, ℝ) → ℝ} (hφ : MemLp φ 2 (s19rMeasure.restrict (s19rDomain Γ)))
    (hψ : MemLp ψ 2 (s19rMeasure.restrict (s19rDomain Γ)))
    (he : φ =ᵐ[s19rMeasure.restrict (s19rDomain Γ)] ψ) (h : SL(2, ℝ)) :
    (fun g => ∑' γ : Γ', (s19rDomain Γ).indicator φ ((γ : SL(2, ℝ)) * g * h))
      =ᵐ[s19rMeasure.restrict (s19rDomain Γ)] fun g => ∑' γ : Γ', (s19rDomain Γ).indicator ψ ((γ : SL(2, ℝ)) * g * h) := by
  have hu := (s19r_rep hΓ hΓ' hneg hrel hrel' (hφ.sub hψ)).1 h
  have hu0 : eLpNorm (φ - ψ) 2 (s19rMeasure.restrict (s19rDomain Γ)) = 0 := by
    have e : φ - ψ =ᵐ[s19rMeasure.restrict (s19rDomain Γ)] 0 :=
      he.mono fun x hx => by rw [Pi.sub_apply, hx, sub_self, Pi.zero_apply]
    rw [eLpNorm_congr_ae e, eLpNorm_zero]
  have hz := (eLpNorm_eq_zero_iff two_ne_zero).mp (hu.2.trans hu0)
  filter_upwards [hz, s19f_single hΓ hΓ' hneg hrel hrel' h] with g hg hs
  obtain ⟨γ₀, -, hγ⟩ := hs
  beta_reduce at hg ⊢
  have h1 := hγ (φ - ψ)
  rw [hg, Pi.zero_apply, Pi.sub_apply] at h1
  rw [hγ, hγ]
  linarith

/-- **F4.** The folded right translate by `h` is a linear isometry of `L²(μ|_D)`. -/
theorem s19f_T {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {Γ' : Subgroup SL(2, ℝ)}
    (hΓ' : LiZhongQC.IsFuchsian Γ') (hneg : -1 ∈ Γ')
    (hrel : ∀ M ∈ Γ', ∃ g ∈ Γ, ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I))
    (hrel' : ∀ g ∈ Γ, ∃ M ∈ Γ', ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I))
    (h : SL(2, ℝ)) :
    ∃ T : Lp ℝ 2 (s19rMeasure.restrict (s19rDomain Γ)) →ₗᵢ[ℝ] Lp ℝ 2 (s19rMeasure.restrict (s19rDomain Γ)),
      ∀ v, (T v : SL(2, ℝ) → ℝ) =ᵐ[s19rMeasure.restrict (s19rDomain Γ)]
        fun g => ∑' γ : Γ', (s19rDomain Γ).indicator (v : SL(2, ℝ) → ℝ) ((γ : SL(2, ℝ)) * g * h) := by
  have hm : ∀ v : Lp ℝ 2 (s19rMeasure.restrict (s19rDomain Γ)),
      MemLp (fun g => ∑' γ : Γ', (s19rDomain Γ).indicator (v : SL(2, ℝ) → ℝ) ((γ : SL(2, ℝ)) * g * h)) 2
        (s19rMeasure.restrict (s19rDomain Γ)) :=
    fun v => ((s19r_rep hΓ hΓ' hneg hrel hrel' (Lp.memLp v)).1 h).1
  refine ⟨{ toFun := fun v => (hm v).toLp _
            map_add' := ?_
            map_smul' := ?_
            norm_map' := ?_ }, fun v => (hm v).coeFn_toLp⟩
  · intro v w
    apply Lp.ext
    have e1 := s19f_fold_congr hΓ hΓ' hneg hrel hrel' (Lp.memLp (v + w)) ((Lp.memLp v).add (Lp.memLp w))
      (Lp.coeFn_add v w) h
    filter_upwards [(hm (v + w)).coeFn_toLp, Lp.coeFn_add ((hm v).toLp _) ((hm w).toLp _), (hm v).coeFn_toLp,
      (hm w).coeFn_toLp, e1, s19f_single hΓ hΓ' hneg hrel hrel' h] with g h1 h2 h3 h4 h5 h6
    obtain ⟨γ₀, -, hγ⟩ := h6
    beta_reduce at h1 h3 h4 h5 ⊢
    rw [h1, h2, Pi.add_apply, h3, h4, h5, hγ, hγ, hγ, Pi.add_apply]
  · intro c v
    apply Lp.ext
    have e1 := s19f_fold_congr hΓ hΓ' hneg hrel hrel' (Lp.memLp (c • v)) ((Lp.memLp v).const_smul c)
      (Lp.coeFn_smul c v) h
    filter_upwards [(hm (c • v)).coeFn_toLp, Lp.coeFn_smul c ((hm v).toLp _), (hm v).coeFn_toLp,
      e1, s19f_single hΓ hΓ' hneg hrel hrel' h] with g h1 h2 h3 h5 h6
    obtain ⟨γ₀, -, hγ⟩ := h6
    beta_reduce at h1 h3 h5 ⊢
    rw [RingHom.id_apply, h1, h2, Pi.smul_apply, h3, h5, hγ, hγ, Pi.smul_apply]
  · intro v
    show ‖(hm v).toLp _‖ = ‖v‖
    rw [Lp.norm_toLp, ((s19r_rep hΓ hΓ' hneg hrel hrel' (Lp.memLp v)).1 h).2, Lp.norm_def]

/-- **F5.** The folded right-regular representation: a jointly continuous isometric representation on `L²(μ|_D)`. -/
theorem s19f_rho {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {Γ' : Subgroup SL(2, ℝ)}
    (hΓ' : LiZhongQC.IsFuchsian Γ') (hneg : -1 ∈ Γ')
    (hrel : ∀ M ∈ Γ', ∃ g ∈ Γ, ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I))
    (hrel' : ∀ g ∈ Γ, ∃ M ∈ Γ', ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I)) :
    ∃ ρ : SL(2, ℝ) →* (Lp ℝ 2 (s19rMeasure.restrict (s19rDomain Γ)) ≃ₗᵢ[ℝ]
        Lp ℝ 2 (s19rMeasure.restrict (s19rDomain Γ))),
      Continuous (fun p : SL(2, ℝ) × Lp ℝ 2 (s19rMeasure.restrict (s19rDomain Γ)) => ρ p.1 p.2) ∧
      ∀ h v, (ρ h v : SL(2, ℝ) → ℝ) =ᵐ[s19rMeasure.restrict (s19rDomain Γ)]
        fun g => ∑' γ : Γ', (s19rDomain Γ).indicator (v : SL(2, ℝ) → ℝ) ((γ : SL(2, ℝ)) * g * h) := by
  choose T hT using s19f_T hΓ hΓ' hneg hrel hrel'
  have hR := fun v : Lp ℝ 2 (s19rMeasure.restrict (s19rDomain Γ)) => s19r_rep hΓ hΓ' hneg hrel hrel' (Lp.memLp v)
  have hcomp : ∀ a b v, T a (T b v) = T (a * b) v := by
    intro a b v
    apply Lp.ext
    have e2 := s19f_fold_congr hΓ hΓ' hneg hrel hrel' (Lp.memLp (T b v)) ((hR v).1 b).1 (hT b v) a
    exact (hT a (T b v)).trans (e2.trans (((hR v).2.1 b a).trans (hT (a * b) v).symm))
  have hone : ∀ v, T 1 v = v := fun v => Lp.ext ((hT 1 v).trans (hR v).2.2.1)
  have hsurj : ∀ h, Function.Surjective (T h) := fun h v =>
    ⟨T h⁻¹ v, by rw [hcomp, mul_inv_cancel, hone]⟩
  -- strong continuity at `1`
  have hsc : ∀ v, Tendsto (fun h => T h v) (𝓝 1) (𝓝 v) := by
    intro v
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have e : ∀ h, ‖T h v - v‖ = (eLpNorm ((fun g => ∑' γ : Γ', (s19rDomain Γ).indicator (v : SL(2, ℝ) → ℝ)
        ((γ : SL(2, ℝ)) * g * h)) - (v : SL(2, ℝ) → ℝ)) 2 (s19rMeasure.restrict (s19rDomain Γ))).toReal := fun h => by
      rw [Lp.norm_def, eLpNorm_congr_ae ((Lp.coeFn_sub _ _).trans ((hT h v).sub (EventuallyEq.refl _ _)))]
    simp only [e]
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hR v).2.2.2
    rwa [ENNReal.toReal_zero] at this
  refine ⟨{ toFun := fun h => LinearIsometryEquiv.ofSurjective (T h) (hsurj h)
            map_one' := LinearIsometryEquiv.ext fun v => hone v
            map_mul' := fun a b => LinearIsometryEquiv.ext fun v => (hcomp a b v).symm }, ?_, fun h v => hT h v⟩
  show Continuous fun p : SL(2, ℝ) × Lp ℝ 2 (s19rMeasure.restrict (s19rDomain Γ)) => T p.1 p.2
  rw [continuous_iff_continuousAt]
  rintro ⟨h₀, v₀⟩
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hb : ∀ p : SL(2, ℝ) × Lp ℝ 2 (s19rMeasure.restrict (s19rDomain Γ)),
      ‖T p.1 p.2 - T (h₀, v₀).1 (h₀, v₀).2‖ ≤ ‖p.2 - v₀‖ + ‖T (h₀⁻¹ * p.1) v₀ - v₀‖ := fun p => by
    have e1 : T p.1 p.2 - T h₀ v₀ = T p.1 (p.2 - v₀) + T h₀ (T (h₀⁻¹ * p.1) v₀ - v₀) := by
      rw [map_sub, map_sub, hcomp, mul_inv_cancel_left]
      abel
    show ‖T p.1 p.2 - T h₀ v₀‖ ≤ _
    rw [e1]
    refine (norm_add_le _ _).trans_eq ?_
    rw [LinearIsometry.norm_map, LinearIsometry.norm_map]
  refine squeeze_zero (fun p => norm_nonneg _) hb ?_
  rw [show (0 : ℝ) = 0 + 0 by norm_num]
  refine Tendsto.add ?_ ?_
  · have : Tendsto (fun p : SL(2, ℝ) × Lp ℝ 2 (s19rMeasure.restrict (s19rDomain Γ)) => p.2) (𝓝 (h₀, v₀)) (𝓝 v₀) :=
      continuous_snd.tendsto _
    exact tendsto_iff_norm_sub_tendsto_zero.mp this
  · have h1 : Tendsto (fun p : SL(2, ℝ) × Lp ℝ 2 (s19rMeasure.restrict (s19rDomain Γ)) => h₀⁻¹ * p.1)
        (𝓝 (h₀, v₀)) (𝓝 1) := by
      have h2 : Tendsto (fun p : SL(2, ℝ) × Lp ℝ 2 (s19rMeasure.restrict (s19rDomain Γ)) => h₀⁻¹ * p.1)
          (𝓝 (h₀, v₀)) (𝓝 (h₀⁻¹ * h₀)) := (continuous_const.mul continuous_fst).tendsto (h₀, v₀)
      rwa [inv_mul_cancel] at h2
    exact tendsto_iff_norm_sub_tendsto_zero.mp ((hsc v₀).comp h1)

/-- **F5b.** `μ(D) = π A(Γ)`. -/
theorem s19f_muD {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {Γ' : Subgroup SL(2, ℝ)}
    (hΓ' : LiZhongQC.IsFuchsian Γ') (hneg : -1 ∈ Γ')
    (hrel : ∀ M ∈ Γ', ∃ g ∈ Γ, ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I))
    (hrel' : ∀ g ∈ Γ, ∃ M ∈ Γ', ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I)) :
    (s19rMeasure (s19rDomain Γ)).toReal = π * (hypArea Γ).toReal := by
  obtain ⟨-, -, -, hint⟩ := s19r_domain hΓ hΓ' hneg hrel hrel'
  have h := hint (fun _ => 1) measurable_const
  simp only [one_mul] at h
  rw [setLIntegral_one] at h
  rw [h, ENNReal.toReal_mul, ENNReal.toReal_ofReal Real.pi_pos.le]
  rfl

/-- **F6.** By R4 (E) the invariant vectors are the constants, so the invariant projection pairs as
`⟪w, P v⟫ = (∫_D w)(∫_D v)/μ(D)`. -/
theorem s19f_proj {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {Γ' : Subgroup SL(2, ℝ)}
    (hΓ' : LiZhongQC.IsFuchsian Γ') (hneg : -1 ∈ Γ')
    (hrel : ∀ M ∈ Γ', ∃ g ∈ Γ, ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I))
    (hrel' : ∀ g ∈ Γ, ∃ M ∈ Γ', ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I))
    (ρ : SL(2, ℝ) →* (Lp ℝ 2 (s19rMeasure.restrict (s19rDomain Γ)) ≃ₗᵢ[ℝ]
        Lp ℝ 2 (s19rMeasure.restrict (s19rDomain Γ))))
    (hρ : ∀ h v, (ρ h v : SL(2, ℝ) → ℝ) =ᵐ[s19rMeasure.restrict (s19rDomain Γ)]
        fun g => ∑' γ : Γ', (s19rDomain Γ).indicator (v : SL(2, ℝ) → ℝ) ((γ : SL(2, ℝ)) * g * h))
    (v w : Lp ℝ 2 (s19rMeasure.restrict (s19rDomain Γ))) :
    inner ℝ w (invariantProjection ρ v) =
      (∫ g in s19rDomain Γ, w g ∂s19rMeasure) * (∫ g in s19rDomain Γ, v g ∂s19rMeasure) /
        (s19rMeasure (s19rDomain Γ)).toReal := by
  have hμD := s19r4_muD hΓ hΓ' hneg hrel hrel'
  haveI : IsFiniteMeasure (s19rMeasure.restrict (s19rDomain Γ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hμD⟩
  have hfin : (s19rMeasure.restrict (s19rDomain Γ)) univ ≠ ⊤ := measure_ne_top _ _
  set e := indicatorConstLp 2 MeasurableSet.univ hfin (1 : ℝ) with hedef
  have he1 : (e : SL(2, ℝ) → ℝ) =ᵐ[s19rMeasure.restrict (s19rDomain Γ)] fun _ => 1 := by
    filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := MeasurableSet.univ) (hμs := hfin) (c := (1 : ℝ))]
      with x hx
    rw [hx, indicator_univ]
  -- the invariant vectors are the multiples of `e`
  have hfix : ∀ x, x ∈ (fixedVectors ρ).toSubmodule ↔ x ∈ (ℝ ∙ e) := by
    intro x
    constructor
    · intro hx
      have hx' : ∀ h, ρ h x = x := hx
      obtain ⟨c, hc⟩ := (s19r_erg_link hΓ hΓ' hneg hrel hrel').1 x (Lp.memLp x)
        (fun h => (hρ h x).symm.trans (by rw [hx' h]))
      refine Submodule.mem_span_singleton.mpr ⟨c, Lp.ext ?_⟩
      filter_upwards [Lp.coeFn_smul c e, he1, hc] with g h1 h2 h3
      rw [h1, Pi.smul_apply, h2, h3, smul_eq_mul, mul_one]
    · intro hx
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
      have hefix : ∀ h, ρ h e = e := by
        intro h
        apply Lp.ext
        have e2 := s19f_fold_congr hΓ hΓ' hneg hrel hrel' (Lp.memLp e) (memLp_const (1 : ℝ)) he1 h
        filter_upwards [hρ h e, e2, he1, s19f_single hΓ hΓ' hneg hrel hrel' h] with g h1 h2 h3 h4
        obtain ⟨γ₀, -, hγ⟩ := h4
        beta_reduce at h2
        rw [h1, h2, hγ, h3]
      show ∀ h, ρ h (c • e) = c • e
      intro h
      rw [map_smul, hefix]
  -- the projection
  have hee : inner ℝ e e = (s19rMeasure (s19rDomain Γ)).toReal := by
    rw [hedef, L2.inner_indicatorConstLp_one, Measure.restrict_univ, integral_congr_ae he1, integral_const,
      smul_eq_mul, mul_one, Measure.real, Measure.restrict_apply_univ]
  have hie : ∀ x : Lp ℝ 2 (s19rMeasure.restrict (s19rDomain Γ)),
      inner ℝ e x = ∫ g in s19rDomain Γ, x g ∂s19rMeasure := fun x => by
    rw [hedef, L2.inner_indicatorConstLp_one, Measure.restrict_univ]
  have hne : inner ℝ e e ≠ 0 := by
    rw [hee, s19f_muD hΓ hΓ' hneg hrel hrel']
    exact mul_ne_zero Real.pi_pos.ne' (pat_hypArea_toReal_pos hΓ).ne'
  have hP : invariantProjection ρ v = (inner ℝ e v / inner ℝ e e) • e := by
    show (fixedVectors ρ).toSubmodule.starProjection v = _
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ((hfix _).mpr
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e))) fun w hw => ?_
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ((hfix w).mp hw)
    rw [inner_smul_right, inner_sub_left, real_inner_smul_left, real_inner_comm e v]
    field_simp
    ring
  rw [hP, real_inner_smul_right, hie v, show inner ℝ w e = inner ℝ e w from real_inner_comm _ _, hie w, hee]
  ring

/-- **F7.** Lifts of bounded measurable functions on `𝔻*` are square integrable on `D`. -/
theorem s19f_lift_mem {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {Γ' : Subgroup SL(2, ℝ)}
    (hΓ' : LiZhongQC.IsFuchsian Γ') (hneg : -1 ∈ Γ')
    (hrel : ∀ M ∈ Γ', ∃ g ∈ Γ, ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I))
    (hrel' : ∀ g ∈ Γ, ∃ M ∈ Γ', ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I))
    {f : ℂ → ℝ} (hfm : Measurable f) {C : ℝ} (hC : ∀ z ∈ unitDiscExterior, |f z| ≤ C) :
    MemLp (fun x : SL(2, ℝ) => f ((((x • UpperHalfPlane.I : ℍ) : ℂ) + I) / (((x • UpperHalfPlane.I : ℍ) : ℂ) - I))) 2
      (s19rMeasure.restrict (s19rDomain Γ)) := by
  have hμD := s19r4_muD hΓ hΓ' hneg hrel hrel'
  haveI : IsFiniteMeasure (s19rMeasure.restrict (s19rDomain Γ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hμD⟩
  have hom := s19r4_orbit_meas
  have hm : Measurable fun x : SL(2, ℝ) =>
      f ((((x • UpperHalfPlane.I : ℍ) : ℂ) + I) / (((x • UpperHalfPlane.I : ℍ) : ℂ) - I)) :=
    hfm.comp ((hom.add_const I).div (hom.sub_const I))
  refine MemLp.of_bound hm.aestronglyMeasurable (max C |f 0|) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  rcases s19r4_cayley_mem (x • UpperHalfPlane.I) with h | h
  · exact (hC _ h).trans (le_max_left _ _)
  · rw [h]; exact le_max_right _ _

/-- **F7b.** Integrals of lifts: `∫_D f(C(x • i)) dμ = π ∬_F f ρ`. -/
theorem s19f_lift_int {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {Γ' : Subgroup SL(2, ℝ)}
    (hΓ' : LiZhongQC.IsFuchsian Γ') (hneg : -1 ∈ Γ')
    (hrel : ∀ M ∈ Γ', ∃ g ∈ Γ, ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I))
    (hrel' : ∀ g ∈ Γ, ∃ M ∈ Γ', ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I))
    {f : ℂ → ℝ} (hfm : Measurable f) {C : ℝ} (hC : ∀ z ∈ unitDiscExterior, |f z| ≤ C) :
    (∫ x in s19rDomain Γ,
        f ((((x • UpperHalfPlane.I : ℍ) : ℂ) + I) / (((x • UpperHalfPlane.I : ℍ) : ℂ) - I)) ∂s19rMeasure) =
      π * ∫ z in fundDomain Γ, f z * rho z := by
  set C' := max C |f 0| with hC'
  have hC0 : 0 ≤ C' := (abs_nonneg _).trans (le_max_right _ _)
  have hclamp : ∀ t : ℝ, |t| ≤ C' → max (-C') (min C' t) = t := fun t ht => by
    obtain ⟨h1, h2⟩ := abs_le.mp ht
    rw [min_eq_right h2, max_eq_right h1]
  have hGm : Measurable fun z => max (-C') (min C' (f z)) :=
    measurable_const.max (measurable_const.min hfm)
  have hGb : ∀ z, |max (-C') (min C' (f z))| ≤ C' := fun z =>
    abs_le.mpr ⟨le_max_left _ _, max_le (neg_le_self hC0) (min_le_left _ _)⟩
  have h1 : (∫ x in s19rDomain Γ,
      f ((((x • UpperHalfPlane.I : ℍ) : ℂ) + I) / (((x • UpperHalfPlane.I : ℍ) : ℂ) - I)) ∂s19rMeasure) =
      ∫ x in s19rDomain Γ, max (-C') (min C' (f ((((x • UpperHalfPlane.I : ℍ) : ℂ) + I) /
        (((x • UpperHalfPlane.I : ℍ) : ℂ) - I)))) ∂s19rMeasure := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    refine (hclamp _ ?_).symm
    beta_reduce
    rcases s19r4_cayley_mem (x • UpperHalfPlane.I) with h | h
    · exact (hC _ h).trans (le_max_left _ _)
    · rw [h]; exact le_max_right _ _
  rw [h1, s19r4_dom_bochner hΓ hΓ' hneg hrel hrel' hGm hGb]
  congr 1
  refine setIntegral_congr_fun (fundDomain_measurable Γ) fun z hz => ?_
  rw [hclamp _ ((hC z (fundDomain_subset Γ hz)).trans (le_max_left _ _))]

/-- **F8.** The fold of the lift of a `Γ`-automorphic function is its right translate, a.e. on `D`. -/
theorem s19f_lift_fold {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {Γ' : Subgroup SL(2, ℝ)}
    (hΓ' : LiZhongQC.IsFuchsian Γ') (hneg : -1 ∈ Γ')
    (hrel : ∀ M ∈ Γ', ∃ g ∈ Γ, ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I))
    (hrel' : ∀ g ∈ Γ, ∃ M ∈ Γ', ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I))
    {f : ℂ → ℝ} (hfa : ∀ γ ∈ Γ, ∀ z ∈ unitDiscExterior, f (mob γ z) = f z) (h : SL(2, ℝ)) :
    (fun g => ∑' γ : Γ', (s19rDomain Γ).indicator
        (fun x : SL(2, ℝ) => f ((((x • UpperHalfPlane.I : ℍ) : ℂ) + I) / (((x • UpperHalfPlane.I : ℍ) : ℂ) - I)))
        ((γ : SL(2, ℝ)) * g * h))
      =ᵐ[s19rMeasure.restrict (s19rDomain Γ)]
      fun g => f (((((g * h) • UpperHalfPlane.I : ℍ) : ℂ) + I) / ((((g * h) • UpperHalfPlane.I : ℍ) : ℂ) - I)) := by
  haveI := s13c_countable hΓ'
  have hNm : MeasurableSet {g : SL(2, ℝ) | ((g • UpperHalfPlane.I : ℍ) : ℂ) ∈ ({I} : Set ℂ)} :=
    s19r4_orbit_meas (measurableSet_singleton I)
  have hN : s19rMeasure {g : SL(2, ℝ) | ((g • UpperHalfPlane.I : ℍ) : ℂ) ∈ ({I} : Set ℂ)} = 0 :=
    s19r_null (measure_singleton I)
  have hNh : s19rMeasure ((fun g => g * h) ⁻¹'
      {g : SL(2, ℝ) | ((g • UpperHalfPlane.I : ℍ) : ℂ) ∈ ({I} : Set ℂ)}) = 0 := by
    rw [← Measure.map_apply (s19r_mul_right_meas h) hNm, s19r_right_inv h, hN]
  have hbad : ∀ γ : Γ', s19rMeasure ((fun g => (γ : SL(2, ℝ)) * g) ⁻¹' ((fun g => g * h) ⁻¹'
      {g : SL(2, ℝ) | ((g • UpperHalfPlane.I : ℍ) : ℂ) ∈ ({I} : Set ℂ)})) = 0 := by
    intro γ
    rw [← Measure.map_apply (s19r_mul_left_meas _) ((s19r_mul_right_meas h) hNm), s19r_left_inv, hNh]
  have hgood : ∀ᵐ g ∂(s19rMeasure.restrict (s19rDomain Γ)),
      ((((g * h) • UpperHalfPlane.I : ℍ) : ℂ) ≠ I) ∧
        ∀ γ : Γ', ((((γ : SL(2, ℝ)) * g * h) • UpperHalfPlane.I : ℍ) : ℂ) ≠ I := by
    refine ae_restrict_of_ae ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hNh,
      ae_all_iff.mpr fun γ => measure_eq_zero_iff_ae_notMem.mp (hbad γ)] with g h1 h2
    exact ⟨h1, h2⟩
  filter_upwards [hgood, s19f_single hΓ hΓ' hneg hrel hrel' h] with g hg hs
  obtain ⟨hgh, hγg⟩ := hg
  obtain ⟨γ₀, -, hγ⟩ := hs
  beta_reduce
  rw [hγ]
  obtain ⟨γ, hγΓ, hmob⟩ := hrel γ₀ γ₀.2
  have hz : ((((g * h) • UpperHalfPlane.I : ℍ) : ℂ) + I) / ((((g * h) • UpperHalfPlane.I : ℍ) : ℂ) - I) ∈
      unitDiscExterior := by
    rcases s19r4_cayley_mem ((g * h) • UpperHalfPlane.I) with hm | hm
    · exact hm
    · exfalso
      rcases div_eq_zero_iff.mp hm with h0 | h0
      · have := congrArg Complex.im h0
        rw [Complex.add_im, Complex.I_im, Complex.zero_im, UpperHalfPlane.coe_im] at this
        linarith [((g * h) • UpperHalfPlane.I).im_pos]
      · exact hgh (sub_eq_zero.mp h0)
  have e : ((γ₀ : SL(2, ℝ)) * g * h) • UpperHalfPlane.I = (γ₀ : SL(2, ℝ)) • ((g * h) • UpperHalfPlane.I) := by
    rw [mul_assoc]; exact mul_smul _ _ _
  have hτ := hγg γ₀
  rw [e] at hτ ⊢
  rw [← hmob _ hgh hτ, hfa γ hγΓ _ hz]

/-- **F9.** The packaged representation `hrep` of `s19c_core_of_rep`: `L²(μ|_D)` for the enlarged transferred group,
the folded right-regular representation, and the lift `L f = π^{-1/2} f ∘ C(· • i)`. -/
theorem s19f_hrep {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) :
    ∃ (X : Type) (_ : MeasurableSpace X) (μ : Measure X)
      (ρ : SL(2, ℝ) →* (Lp ℝ 2 μ ≃ₗᵢ[ℝ] Lp ℝ 2 μ)) (L : (ℂ → ℝ) → Lp ℝ 2 μ),
      Continuous (fun p : SL(2, ℝ) × Lp ℝ 2 μ => ρ p.1 p.2) ∧
      ∀ f g : ℂ → ℝ, Measurable f → Measurable g →
        (∃ C, ∀ z ∈ unitDiscExterior, |f z| ≤ C) → (∃ C, ∀ z ∈ unitDiscExterior, |g z| ≤ C) →
        (∀ γ ∈ Γ, ∀ z ∈ unitDiscExterior, f (mob γ z) = f z) →
        (∀ γ ∈ Γ, ∀ z ∈ unitDiscExterior, g (mob γ z) = g z) →
        inner ℝ (L g) (invariantProjection ρ (L f)) =
            (∫ z in fundDomain Γ, f z * rho z) * (∫ z in fundDomain Γ, g z * rho z) / (hypArea Γ).toReal ∧
          ∀ u ∈ Ioo (0 : ℝ) 1,
            (∫ z in fundDomain Γ, (∫ θ in (0 : ℝ)..2 * π,
                f ((z * (exp (θ * I) / u) + 1) / (exp (θ * I) / u + conj z))) / (2 * π) * g z * rho z) =
              inner ℝ (L g) (ρ (mautnerDiag (√((1 - u) / (1 + u))))⁻¹ (L f)) := by
  obtain ⟨Γ₀, hF0, hr0, hr0'⟩ := s13c_transfer_group hΓ.1
  obtain ⟨Γ', hΓ', hneg, hrel, hrel'⟩ := s19f_enlarge hF0 hr0 hr0'
  obtain ⟨ρ, hcont, hρ⟩ := s19f_rho hΓ hΓ' hneg hrel hrel'
  -- `L f = π^{-1/2} f ∘ C(· • i)`. The `else 0` branch is junk and never used: below, `L` is only applied to
  -- bounded measurable `f`, whose lifts are in `L²` by `s19f_lift_mem`, so both uses go through `dif_pos`.
  refine ⟨SL(2, ℝ), inferInstance, s19rMeasure.restrict (s19rDomain Γ), ρ, fun f =>
    if hf : MemLp (fun x : SL(2, ℝ) =>
        f ((((x • UpperHalfPlane.I : ℍ) : ℂ) + I) / (((x • UpperHalfPlane.I : ℍ) : ℂ) - I))) 2
      (s19rMeasure.restrict (s19rDomain Γ)) then (1 / √π) • hf.toLp _ else 0, hcont, ?_⟩
  intro f g hfm hgm hfb hgb hfa hga
  obtain ⟨Cf, hCf⟩ := hfb
  obtain ⟨Cg, hCg⟩ := hgb
  have hLf := s19f_lift_mem hΓ hΓ' hneg hrel hrel' hfm hCf
  have hLg := s19f_lift_mem hΓ hΓ' hneg hrel hrel' hgm hCg
  beta_reduce
  rw [dif_pos hLf, dif_pos hLg]
  have hπ := Real.pi_pos
  have hc : (1 / √π) * (1 / √π) = 1 / π := by
    rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt hπ.le]
  have hA := pat_hypArea_toReal_pos hΓ
  have hIf : (∫ x in s19rDomain Γ, (hLf.toLp _ : SL(2, ℝ) → ℝ) x ∂s19rMeasure) =
      π * ∫ z in fundDomain Γ, f z * rho z := by
    rw [integral_congr_ae hLf.coeFn_toLp]
    exact s19f_lift_int hΓ hΓ' hneg hrel hrel' hfm hCf
  have hIg : (∫ x in s19rDomain Γ, (hLg.toLp _ : SL(2, ℝ) → ℝ) x ∂s19rMeasure) =
      π * ∫ z in fundDomain Γ, g z * rho z := by
    rw [integral_congr_ae hLg.coeFn_toLp]
    exact s19f_lift_int hΓ hΓ' hneg hrel hrel' hgm hCg
  refine ⟨?_, fun u hu => ?_⟩
  · rw [map_smul, real_inner_smul_left, real_inner_smul_right, s19f_proj hΓ hΓ' hneg hrel hrel' ρ hρ, hIf, hIg,
      s19f_muD hΓ hΓ' hneg hrel hrel', ← mul_assoc, hc]
    field_simp
  · rw [map_smul, real_inner_smul_left, real_inner_smul_right, ← mul_assoc, hc]
    have hin : inner ℝ (hLg.toLp _) (ρ (mautnerDiag (√((1 - u) / (1 + u))))⁻¹ (hLf.toLp _)) =
        ∫ x in s19rDomain Γ,
          g ((((x • UpperHalfPlane.I : ℍ) : ℂ) + I) / (((x • UpperHalfPlane.I : ℍ) : ℂ) - I)) *
            f (((((x * (mautnerDiag (√((1 - u) / (1 + u))))⁻¹) • UpperHalfPlane.I : ℍ) : ℂ) + I) /
              ((((x * (mautnerDiag (√((1 - u) / (1 + u))))⁻¹) • UpperHalfPlane.I : ℍ) : ℂ) - I)) ∂s19rMeasure := by
      rw [L2.inner_def]
      refine integral_congr_ae ?_
      have e2 := s19f_fold_congr hΓ hΓ' hneg hrel hrel' (Lp.memLp (hLf.toLp _)) hLf hLf.coeFn_toLp
        (mautnerDiag (√((1 - u) / (1 + u))))⁻¹
      filter_upwards [hLg.coeFn_toLp, hρ (mautnerDiag (√((1 - u) / (1 + u))))⁻¹ (hLf.toLp _), e2,
        s19f_lift_fold hΓ hΓ' hneg hrel hrel' hfa (mautnerDiag (√((1 - u) / (1 + u))))⁻¹] with x h1 h2 h3 h4
      beta_reduce at h1 h3 h4 ⊢
      rw [Real.inner_apply, h1, h2, h3, h4]
    rw [hin, (s19r_erg_link hΓ hΓ' hneg hrel hrel').2 f g hfm hgm ⟨Cf, hCf⟩ ⟨Cg, hCg⟩ hfa hga u hu,
      ← mul_assoc, one_div_mul_cancel hπ.ne', one_mul]

/-- **Lemma 1.9**, unconditional (the statement of `lemma_1_9` of `S1_3_Fuchsian`, for relocation). -/
theorem s19f_lemma_1_9 {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {h : ℂ → ℂ}
    (hmeas : AEStronglyMeasurable h (volume.restrict unitDiscExterior))
    (hbdd : ∃ C, ∀ᵐ z ∂(volume.restrict unitDiscExterior), ‖h z‖ ≤ C)
    (haut : ∀ g ∈ Γ, ∀ᵐ z ∂(volume.restrict unitDiscExterior), h (mob g z) = h z) :
    Tendsto (fun r : ℝ => ((hypArea Γ).toReal / (∫ z in discExteriorR r, rho z) : ℂ) *
        ∫ z in discExteriorR r, h z * rho z)
      (𝓝[>] 1) (𝓝 (quotientIntegral Γ fun z => h z * rho z)) :=
  s19m_lemma_1_9_of_core hΓ hmeas hbdd haut (s19c_core_of_inv hΓ (s19c_core_of_rep hΓ (s19f_hrep hΓ)))

/-- **Lemma 1.9** (Patterson [Pat75], in the form of [Teo04]) (TT:1056–1062). Let `Γ` be cofinite and `h` a bounded
measurable `Γ`-automorphic function on `𝔻*` (`h ∘ γ = h`). Then
`∬_{Γ\𝔻*} h ρ d²z = lim_{r → 1⁺} (A(Γ\𝔻*)/A(𝔻*_r)) ∬_{𝔻*_r} h ρ d²z`. -/
theorem lemma_1_9 {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {h : ℂ → ℂ}
    (hmeas : AEStronglyMeasurable h (volume.restrict unitDiscExterior))
    (hbdd : ∃ C, ∀ᵐ z ∂(volume.restrict unitDiscExterior), ‖h z‖ ≤ C)
    (haut : ∀ g ∈ Γ, ∀ᵐ z ∂(volume.restrict unitDiscExterior), h (mob g z) = h z) :
    Tendsto (fun r : ℝ => ((hypArea Γ).toReal / (∫ z in discExteriorR r, rho z) : ℂ) *
        ∫ z in discExteriorR r, h z * rho z)
      (𝓝[>] 1) (𝓝 (quotientIntegral Γ fun z => h z * rho z)) :=
  s19f_lemma_1_9 hΓ hmeas hbdd haut

end TakhtajanTeo
