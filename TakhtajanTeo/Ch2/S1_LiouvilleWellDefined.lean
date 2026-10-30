import TakhtajanTeo.Ch1.ComponentTC
import TakhtajanTeo.Ch1.Cor32Completed
import TakhtajanTeo.Ch2.S1_T112Completed

/-!
# Liouville S1 well-definedness from the one-way T01 inclusion

The component inclusion gives Bers A2 membership. The disk analytic implication,
inversion preserving T01, and the exterior class equivalence give both A21 norms.
The full Corollary 3.2 and Theorem 1.12 are not invoked. The prefixed final theorem
has the exact original statement; installation of the original name is separate.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo.Ch2
open LiZhongQC

/-- Only the proved component inclusion is used; no converse A2-to-T01 assertion is needed. -/
theorem ls1wd_bers_A2 {p : T1} (hp : p∈T01) : AInf.toFun (bers p)∈A2fun unitDisc := by
  have hspec := ctd_componentT_spec_one_subset (Phi ⟨0,mem_ball_self one_pos⟩)
    (show bers p∈bers '' componentT (Phi ⟨0,mem_ball_self one_pos⟩) from ⟨p,hp,rfl⟩)
  obtain ⟨⟨ψ,hψ⟩,_⟩ := hspec
  rw [c32_bers_origin,zero_add] at hψ
  exact ctc_mem_range.mpr ⟨ψ,hψ.symm⟩

theorem ls1wd_preSchwarzian_disc {p : T1} (hp : p∈T01) :
    preSchwarzian (fsans ((Quotient.out p : LinfStarBall) : LinfStar))∈A21fun unitDisc := by
  have hμ := (Quotient.out p : LinfStarBall).2
  obtain ⟨hd,hi,hJ,hb⟩ := ab112_fsans_facts hμ
  have hS := (ab112_A2fun_congr (show IsOpen unitDisc from isOpen_ball)
    (fun z hz => ab112_bers_eq p z hz)).mp (ls1wd_bers_A2 hp)
  exact ab112_lemma_1_11_f hd hi hJ hb hS

theorem ls1wd_preSchwarzian_exterior {p : T1} (hp : p∈T01) :
    preSchwarzian (gsans ((Quotient.out p : LinfStarBall) : LinfStar))∈A21fun unitDiscExterior := by
  have hν := (Quotient.out (invT p) : LinfStarBall).2
  have hA := ls1wd_preSchwarzian_disc (grp_lemma_3_4.2.2 p hp)
  have hG := (ab112_A_G_iff hν).mpr hA
  have hrel : teichSetoid
      ⟨beltramiInv ((Quotient.out (invT p) : LinfStarBall) : LinfStar),bc_beltramiInv_mem_ball hν⟩
      (Quotient.out p : LinfStarBall) := by
    apply Quotient.exact
    change Phi ⟨beltramiInv ((Quotient.out (invT p) : LinfStarBall) : LinfStar),
      bc_beltramiInv_mem_ball hν⟩=Phi (Quotient.out p : LinfStarBall)
    rw [← ab112_invT_eq (invT p),grp_invT_invT p]
    exact (Quotient.out_eq p).symm
  have hE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  exact (ab112_A21fun_congr hE (ab112_P_eqOn hE (s2c_class_pair hrel).2)).mp hG

theorem ls1wd_liouvilleS1_wellDefined {p : T1} (hp : p ∈ T01) :
    let μ : LinfStar := (Quotient.out p : LinfStarBall)
    IntegrableOn (fun z => ‖preSchwarzian (fsans μ) z‖ ^ 2) unitDisc ∧
      IntegrableOn (fun z => ‖preSchwarzian (gsans μ) z‖ ^ 2) unitDiscExterior ∧ derivAtInfty (gsans μ) ≠ 0 := by
  dsimp only
  refine ⟨a21_integrable_sq (show MeasurableSet unitDisc from measurableSet_ball)
      (ls1wd_preSchwarzian_disc hp),
    a21_integrable_sq (isOpen_lt continuous_const continuous_norm).measurableSet
      (ls1wd_preSchwarzian_exterior hp),?_⟩
  have hpair := AppB.b8_welding_normalized_pair (Quotient.out p : LinfStarBall).2
  rw [← (grunsky_spec hpair).1.1]
  exact Complex.exp_ne_zero _

end TakhtajanTeo.Ch2
