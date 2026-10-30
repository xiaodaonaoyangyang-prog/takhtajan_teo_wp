import TakhtajanTeo.Ch1.S3_TopologicalGroup
import TakhtajanTeo.Ch1.BersInjective
import TakhtajanTeo.Ch1.QCVariationSurjSmall

/-!
# Corollary 3.2, proved downstream of §3 (TT:1924–1927)

`c32_cor_3_2` is `cor_3_2`: by `componentT_spec` at the origin, `β(T₀(1)) = A₂(𝔻) ∩ β(T(1))`, and `β` is injective.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- `β([0]) = 0`. -/
theorem c32_bers_origin : bers (Phi ⟨0, mem_ball_self one_pos⟩) = 0 := by
  rw [bers_Phi]
  exact QCV.qs_bersPhi_zero

-- `c32_cor_3_2` removed (2026-10-29, Program G): it depended on the then-unproved `componentT_spec`; the installed
-- `cor_3_2` (HilbertManifoldCompleted) is `hbSurj_cor_3_2`. No consumers.

end TakhtajanTeo
