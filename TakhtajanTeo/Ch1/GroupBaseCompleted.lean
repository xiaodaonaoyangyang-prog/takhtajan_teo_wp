import TakhtajanTeo.Ch1.GroupBaseSequence
import TakhtajanTeo.Ch1.GroupBaseSequential

/-! S3: the unconditional origin density estimate for harmonic coefficients. -/
open Complex Set Filter Topology
namespace TakhtajanTeo
open LiZhongQC

theorem grp25_base : ∀ ε > 0, ∃ δ > 0, ∀ μ ∈ harmonicBeltrami, ‖μ‖ < δ →
    |‖dz (wA μ) 0‖ ^ 2 / (1 - ‖wA μ 0‖ ^ 2) ^ 2 - 1| < ε :=
  grp25_base_of_sequences (fun μ hμ hlim =>
    grp25b_sequence (fun n => (hμ n).1) (fun n => (hμ n).2) hlim)

end TakhtajanTeo

#print axioms TakhtajanTeo.grp25_base
