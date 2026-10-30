# Weil–Petersson Metric on the Universal Teichmüller Space — a Lean 4 formalization

A complete formalization in **Lean 4 / Mathlib** of the memoir

> L. A. Takhtajan, L.-P. Teo, *Weil–Petersson Metric on the Universal Teichmüller Space*,
> Memoirs of the American Mathematical Society **183** (2006), no. 861.

Every definition, theorem, lemma, corollary, proposition and asserting formula of the memoir is stated in Lean and
**proved with no `sorry`**. The full `lake build` succeeds, and the results depend only on Lean's standard axioms
(`propext`, `Classical.choice`, `Quot.sound`).

## What is covered

- **Chapter 1** — the Hilbert manifold structure on the universal Teichmüller space `T(1)`:
  - Beltrami differentials and quasiconformal welding;
  - the Bers embedding and its Hilbert-space atlas;
  - the connected components `T_t(1)` and the subgroups `T_0(1)`, `S¹\Möb(S¹)`;
  - the Weil–Petersson metric and its Kähler property.
- **Chapter 2** — the Weil–Petersson geometry of `T_0(1)`:
  - Ricci and sectional curvature formulas;
  - the universal Liouville action as a Kähler potential;
  - the period mapping and the Grunsky operator, with the formula `det(1 − B̄B)`;
  - the density / approximation results (Thm 3.8 and its corollaries).
- **Appendix** — the analytic background: Banach and Hilbert-space holomorphy, the reproducing kernels and the
  completed function spaces.

Places where the memoir is wrong or uses an unstated hypothesis were corrected faithfully. Each correction is logged
in [`collaboration/ERRATA.md`](collaboration/ERRATA.md) and
[`collaboration/STATEMENT_CHANGES.md`](collaboration/STATEMENT_CHANGES.md).

## Size

| Item | Count |
|---|---|
| Lean source files | ~550 |
| Lines of Lean | ~260k |
| Theorems and lemmas | ~7,900 |
| Definitions | ~500 |
| Open `sorry` | 0 |

## Build

- Lean `v4.35.0-rc2`, Mathlib `2f3d8f6`.
- The project depends on the companion formalization of Li Zhong's *Quasiconformal Mappings and Teichmüller Spaces*
  (library `LiZhongQC`). It supplies quasiconformal maps, the measurable Riemann mapping theorem, Schwarzian
  derivatives and Möbius geometry.
- [`lakefile.toml`](lakefile.toml) points at local checkouts. Adjust the paths, then run `lake build TakhtajanTeo`.

Layout: `TakhtajanTeo/Ch1`, `TakhtajanTeo/Ch2`, `TakhtajanTeo/Appendix`, with the root module
[`TakhtajanTeo.lean`](TakhtajanTeo.lean). [`ARCHITECTURE.md`](ARCHITECTURE.md) describes the modelling conventions.

## Keywords

Lean 4 · Mathlib · formalization · formal verification · interactive theorem proving · formalized mathematics ·
Teichmüller theory · universal Teichmüller space · Weil–Petersson metric · Takhtajan–Teo · quasiconformal mappings ·
Beltrami equation · Beltrami differentials · quasisymmetric homeomorphisms · conformal welding · Bers embedding ·
Schwarzian derivative · Hilbert manifold · Kähler geometry · Ricci curvature · sectional curvature ·
universal Liouville action · Grunsky operator · period mapping · Velling–Kirillov metric · complex analysis ·
geometric function theory · Riemann surfaces · string theory
