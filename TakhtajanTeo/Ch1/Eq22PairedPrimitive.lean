import Mathlib

open Complex
namespace TakhtajanTeo

noncomputable def eq22PairedPrimitive (Q1 Q2 Q3 : ℂ → ℂ) (z u v : ℂ) : ℂ :=
  (Q1 v * (u-v)^2 + 2 * Q2 v * (u-v) + 2 * Q3 v) / (u-z)^3 +
  (Q1 v * (u-v) + Q2 v) / (u-z)^2 + Q1 v / (u-z)

theorem eq22_paired_kernel_split {u v z : ℂ} (hu : u-z ≠ 0) (hv : v-z ≠ 0) :
    1/(u-z) + (u-v)/(u-z)^2 + (u-v)^2/(u-z)^3 =
      1/(v-z) - (u-v)^3/((u-z)^3*(v-z)) := by
  field_simp
  <;> ring

theorem eq22_paired_hasDerivAt {u v : ℝ → ℂ} {U V q z : ℂ} {t : ℝ}
    {Q1 Q2 Q3 : ℂ → ℂ} (hu : HasDerivAt u U t) (hv : HasDerivAt v V t)
    (h1 : HasDerivAt Q1 q (v t)) (h2 : HasDerivAt Q2 (Q1 (v t)) (v t))
    (h3 : HasDerivAt Q3 (Q2 (v t)) (v t)) (hz : u t-z ≠ 0) :
    HasDerivAt (fun s => eq22PairedPrimitive Q1 Q2 Q3 z (u s) (v s))
      (-3 * ((Q1 (v t)*(u t-v t)^2 + 2*Q2 (v t)*(u t-v t) + 2*Q3 (v t)) /
        (u t-z)^4) * U + q * (1/(u t-z) + (u t-v t)/(u t-z)^2 +
        (u t-v t)^2/(u t-z)^3) * V) t := by
  have hQ1 : HasDerivAt (fun s => Q1 (v s)) (V*q) t := by
    simpa only [Function.comp_def, smul_eq_mul] using h1.scomp t hv
  have hQ2 : HasDerivAt (fun s => Q2 (v s)) (V*Q1 (v t)) t := by
    simpa only [Function.comp_def, smul_eq_mul] using h2.scomp t hv
  have hQ3 : HasDerivAt (fun s => Q3 (v s)) (V*Q2 (v t)) t := by
    simpa only [Function.comp_def, smul_eq_mul] using h3.scomp t hv
  have hd := hu.sub hv
  have ha := hu.sub_const z
  have hN := ((hQ1.mul (hd.pow 2)).add ((hQ2.const_mul 2).mul hd)).add
    (hQ3.const_mul 2)
  have hL := (hQ1.mul hd).add hQ2
  have ht := ((hN.div (ha.pow 3) (pow_ne_zero 3 hz)).add
    (hL.div (ha.pow 2) (pow_ne_zero 2 hz))).add (hQ1.div ha hz)
  convert ht using 1
  · funext s
    dsimp [eq22PairedPrimitive]
  · dsimp
    field_simp
    <;> ring

theorem eq22_paired_transfer_hasDerivAt {u v : ℝ → ℂ} {U V q z : ℂ} {t : ℝ}
    {Q1 Q2 Q3 : ℂ → ℂ} (hu : HasDerivAt u U t) (hv : HasDerivAt v V t)
    (h1 : HasDerivAt Q1 q (v t)) (h2 : HasDerivAt Q2 (Q1 (v t)) (v t))
    (h3 : HasDerivAt Q3 (Q2 (v t)) (v t)) (hz : u t-z ≠ 0) (hvz : v t-z ≠ 0) :
    HasDerivAt (fun s => eq22PairedPrimitive Q1 Q2 Q3 z (u s) (v s))
      (-3 * ((Q1 (v t)*(u t-v t)^2 + 2*Q2 (v t)*(u t-v t) + 2*Q3 (v t)) /
        (u t-z)^4) * U + q/(v t-z)*V -
        q*(u t-v t)^3/((u t-z)^3*(v t-z))*V) t := by
  have hd := eq22_paired_hasDerivAt hu hv h1 h2 h3 hz
  rw [eq22_paired_kernel_split hz hvz] at hd
  convert hd using 1 <;> ring

end TakhtajanTeo
