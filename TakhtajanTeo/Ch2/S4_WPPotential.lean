import TakhtajanTeo.Ch2.S3_Variations

/-!
# Chapter 2, §4 — Weil–Petersson potential (TT:5294–5409)

* §4.1 Theorem 4.1, (4.1) and the variational formula in its proof, Corollary 4.2, Remark 4.3, Remark 4.4
* §4.2 the Weil–Petersson potential `S` on `T(1)`

**Modelling.**
- Second derivatives in the Bers coordinates of the chart `V_κ` at its centre are `bersDzDzbar` (§3).
- `ω_WP` at the centre of `V_κ` is `omegaWPOrigin` (Chapter 1, §4): the Weil–Petersson metric is right invariant, and
  in the chart `V_κ` the tangent vectors at `[κ]` are the `μ ∈ H^{-1,1}(𝔻*)`.
- For maps that are not holomorphic (the q.c. maps `w_{εν}`), the Schwarzian in (4.1) is taken with `∂_z` derivatives
  (`schwarzianDz`).
- In Remark 4.4 the derivative `L_ν ϑ` is written in the form of TT:5378. It is a principal value integral (the kernel
  is `O(|w - z|⁻²)` at `w = z`).
- §4.2:
  - the components `T_α(1)` of `T(1)` are the connected components of the Hilbert manifold topology (`componentT`);
  - the base points `[μ_α]` are chosen by `Classical.epsilon` from the component, so they depend only on the component;
  - `μ₀ = 0` for `T₀(1)`.

**Not stated.** The comparison in Remark 4.3 with the local index theorem on compact Riemann surfaces ([ZT87]).
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

namespace Ch2

-- `thm_4_1` moved to `TakhtajanTeo.Ch2.S3Density` (2026-10-29, Program G).

/-- The Schwarzian `(w_{zz}/w_z)_z - ½(w_{zz}/w_z)²` of a (not necessarily holomorphic) map, with `∂_z` derivatives. -/
def schwarzianDz (w : ℂ → ℂ) (z : ℂ) : ℂ :=
  dz (fun u => dz (dz w) u / dz w u) z - (1 / 2) * (dz (dz w) z / dz w z) ^ 2

-- `eq_4_1` moved to `Ch2/S4Eq41.lean` (2026-10-28).

-- `thm_4_1_variation` moved unchanged to `Ch2/S4VariationCompleted.lean` (2026-10-28).

-- `cor_4_2` moved to `TakhtajanTeo.Ch2.S3Density` (2026-10-29, Program G).

-- `remark_4_3` moved to `TakhtajanTeo.Ch2.S4GThm41` (2026-10-29, Program G).

/-- The derivative `(L_ν ϑ)(z) = ∂/∂ε|_{ε=0} 𝒮(g_ε) ∘ w_{εν} (w_{εν})_z²(z)` of `ϑ` at `[κ]` along `ν` (TT:5376). -/
def lieTheta (κ : LinfStar) (ν : ℂ → ℂ) (z : ℂ) : ℂ :=
  dz (fun e => schwarzianHol (gsans (beltramiMul (e • toLinf ν) κ)) (wA (e • toLinf ν) z) *
    dz (wA (e • toLinf ν)) z ^ 2) 0

-- `remark_4_4` moved to `TakhtajanTeo.Ch2.S4GRemark44` (2026-10-29, Program G).

/-- The base point `[μ_α]` of the component `T_α(1)` of `p` (TT:5398): the origin for `T₀(1)`, otherwise a point of
the component chosen by `Classical.epsilon` (so it depends only on the component). -/
def componentBase (p : T1) : T1 :=
  if componentT p = T01 then originT else Classical.epsilon fun q => q ∈ componentT p

-- `componentBase_spec` moved to `Ch2/S4_Completed.lean` (2026-10-27).

/-- The Weil–Petersson potential on `T(1)` (TT:5402–5406): `S([ν]) = S₁([ν * μ_α⁻¹])` for `[ν] ∈ T_α(1)`. -/
def wpPotential (p : T1) : ℝ := liouvilleS1 (mulT p (invT (componentBase p)))

-- `wpPotential_spec` moved to `TakhtajanTeo.Ch2.S3Density` (2026-10-29, Program G).

end Ch2

end TakhtajanTeo
