import TakhtajanTeo.Ch1.Eq22Reproducing

/-! Quantitative boundary-error estimates for the paired primitive in (2.2). -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal Classical Real ComplexConjugate
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- The cubic displacement factor gains one inverse hyperbolic density. -/
theorem eq22_cubic_displacement_bound {q u v : ℂ} {Q D ρ : ℝ}
    (hQ : 0 ≤ Q) (hρ : 0 < ρ)
    (hq : ‖q‖ ≤ Q*ρ^2) (hgeom : ‖u-v‖*ρ ≤ D) :
    ‖q‖*‖u-v‖^3 ≤ Q*D^3/ρ := by
  apply (le_div_iff₀ hρ).mpr
  calc
    ‖q‖*‖u-v‖^3*ρ ≤ (Q*ρ^2)*‖u-v‖^3*ρ := by gcongr
    _ = Q*(‖u-v‖*ρ)^3 := by ring
    _ ≤ Q*D^3 := by gcongr

/-- Exact density transport cancels the radial cutoff derivative loss. -/
theorem eq22_cutoff_density_bound {s t : ℂ} {ρ δ ε M : ℝ}
    (hρ : 0 < ρ) (hδ : 0 ≤ δ) (hε : 0 < ε) (hM : 0 ≤ M)
    (hdensity : ρ*δ*‖s‖ = 2) (hcollar : δ ≤ 2*ε)
    (hcut : ‖t‖*‖s‖ ≤ M/ε) : ‖t‖/ρ ≤ M := by
  have he : ‖t‖/ρ = δ*(‖t‖*‖s‖)/2 := by
    apply (div_eq_iff hρ.ne').mpr
    calc
      ‖t‖ = (‖t‖/2)*2 := by ring
      _ = (‖t‖/2)*(ρ*δ*‖s‖) := by rw [hdensity]
      _ = δ*(‖t‖*‖s‖)/2*ρ := by ring
  rw [he]
  calc
    δ*(‖t‖*‖s‖)/2 ≤ δ*(M/ε)/2 := by gcongr
    _ ≤ (2*ε)*(M/ε)/2 := by gcongr
    _ = M := by field_simp

/-- The pulled-back paired-kernel remainder is dominated by conformal area. -/
theorem eq22_boundary_remainder_bound {q u v z s t : ℂ} {ρ δ ε Q D M a : ℝ}
    (hρ : 0 < ρ) (hδ : 0 ≤ δ) (hε : 0 < ε)
    (hQ : 0 ≤ Q) (hD : 0 ≤ D) (hM : 0 ≤ M) (ha : 0 < a)
    (hdensity : ρ*δ*‖s‖ = 2) (hcollar : δ ≤ 2*ε)
    (hq : ‖q‖ ≤ Q*ρ^2) (hgeom : ‖u-v‖*ρ ≤ D)
    (hcut : ‖t‖*‖s‖ ≤ M/ε)
    (huz : a ≤ ‖u-z‖) (hvz : a ≤ ‖v-z‖) :
    ‖q*(u-v)^3/((u-z)^3*(v-z))*t*s^2‖ ≤
      (Q*D^3*M/a^4)*‖s‖^2 := by
  have hprod : ‖q‖*‖u-v‖^3*‖t‖ ≤ Q*D^3*M := by
    calc
      ‖q‖*‖u-v‖^3*‖t‖ ≤ (Q*D^3/ρ)*‖t‖ :=
        mul_le_mul_of_nonneg_right (eq22_cubic_displacement_bound hQ hρ hq hgeom) (norm_nonneg _)
      _ = (Q*D^3)*(‖t‖/ρ) := by ring
      _ ≤ Q*D^3*M := mul_le_mul_of_nonneg_left
        (eq22_cutoff_density_bound hρ hδ hε hM hdensity hcollar hcut) (by positivity)
  have hden : a^4 ≤ ‖u-z‖^3*‖v-z‖ := by
    calc a^4 = a^3*a := by ring
         _ ≤ ‖u-z‖^3*‖v-z‖ := by gcongr
  simp only [norm_mul,norm_div,norm_pow]
  calc
    ‖q‖*‖u-v‖^3/(‖u-z‖^3*‖v-z‖)*‖t‖*‖s‖^2 =
        (‖q‖*‖u-v‖^3*‖t‖/(‖u-z‖^3*‖v-z‖))*‖s‖^2 := by ring
    _ ≤ (Q*D^3*M/a^4)*‖s‖^2 := by gcongr

end TakhtajanTeo
