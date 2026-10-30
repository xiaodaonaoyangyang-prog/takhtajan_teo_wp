import TakhtajanTeo.Ch1.GroupBaseCompleted
import TakhtajanTeo.Ch1.GroupEstimateAssembly

/-! The guarded Lemma 2.5 estimate, with both origin inputs now discharged. -/
open Complex Set Filter Topology
namespace TakhtajanTeo

/-- Unconditional estimate used to release the group-chain proofs without an import cycle. -/
theorem grp25_lemma_2_5 {ε : ℝ} (hε : 0 < ε) : ∃ δ, Lemma25Prop ε δ := by
  exact grp25a_lemma_2_5_of_origin
    (fun μ hμ hμ1 => (grp25_regular_zero hμ hμ1).1) grp25_base ε hε

end TakhtajanTeo
#print axioms TakhtajanTeo.grp25_lemma_2_5
