import TakhtajanTeo.Ch2.S3_Variations
import TakhtajanTeo.Ch2.S3_Completed
import TakhtajanTeo.Ch2.S1_Theorem112Completed

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC
namespace Ch2

/-- (TT:4664) `ϑ_{[μ]} ∈ A₂(𝔻*)` exactly on `T₀(1)` (Theorem 1.12), and it does not depend on the representative of
`[μ]`.
Proved here as `s3v_vartheta_spec`; statement identical to `vartheta_spec`. -/
theorem s3v_vartheta_spec (p : T1) :
    (p ∈ T01 ↔ vartheta p ∈ A2fun unitDiscExterior) ∧
      ∀ ν : LinfStarBall, Phi ν = p → EqOn (schwarzianHol (gsans (ν : LinfStar))) (vartheta p) unitDiscExterior := by
  refine ⟨(thm_1_12 p).2.2.1, ?_⟩
  intro ν hν z hz
  have hs : teichSetoid ν (Quotient.out p) := Quotient.exact (hν.trans (Quotient.out_eq p).symm)
  have hg := (s2c_class_pair hs).2
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  exact schwarzianHol_congr (Filter.eventuallyEq_of_mem (hEo.mem_nhds hz) hg)

/-- (TT:4664) `ϑ_{[μ]} ∈ A₂(𝔻*)` exactly on `T₀(1)` (Theorem 1.12), and it does not depend on the representative of
`[μ]`. -/
theorem vartheta_spec (p : T1) :
    (p ∈ T01 ↔ vartheta p ∈ A2fun unitDiscExterior) ∧
      ∀ ν : LinfStarBall, Phi ν = p → EqOn (schwarzianHol (gsans (ν : LinfStar))) (vartheta p) unitDiscExterior :=
  s3v_vartheta_spec p

end Ch2

end TakhtajanTeo
