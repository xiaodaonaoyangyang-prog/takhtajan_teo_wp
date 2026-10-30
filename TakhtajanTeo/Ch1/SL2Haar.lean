import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Tactic.NormNum

open Matrix MeasureTheory MeasureTheory.Measure
open scoped MatrixGroups NNReal
noncomputable section
namespace TakhtajanTeo

/-- SL₂(ℝ) is a closed subspace of the finite-dimensional real matrix space. -/
instance sl2R_locallyCompactSpace : LocallyCompactSpace SL(2, ℝ) := by
  letI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → ℝ))
  exact (SpecialLinearGroup.isClosedEmbedding_val (n := Fin 2) (R := ℝ)).locallyCompactSpace

instance sl2R_secondCountableTopology : SecondCountableTopology SL(2, ℝ) := by
  letI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℝ))
  exact (SpecialLinearGroup.isClosedEmbedding_val (n := Fin 2) (R := ℝ)).isEmbedding.secondCountableTopology

/-- Perfectness makes every commutative-monoid character trivial. Passing through
units avoids requiring a group structure on the target monoid itself. -/
theorem sl2R_commutative_character_trivial {M : Type*} [CommMonoid M]
    (f : SL(2, ℝ) →* M) (g : SL(2, ℝ)) : f g = 1 := by
  have hc := Abelianization.commutator_subset_ker f.toHomUnits
  rw [Matrix.SL2.commutator_eq_top (a := (2 : ℝ)) (by norm_num) (by norm_num)] at hc
  have hg : f.toHomUnits g = 1 := MonoidHom.mem_ker.mp (hc (Subgroup.mem_top g))
  exact congrArg (fun u : Mˣ => (u : M)) hg

theorem sl2R_modularCharacter_eq_one (g : SL(2, ℝ)) :
    modularCharacterFun g = 1 :=
  sl2R_commutative_character_trivial modularCharacter g

/-- Actual right invariance of any inner-regular left Haar measure on SL₂(ℝ).
Unimodularity is a conclusion, not an added assumption. -/
theorem sl2R_haar_right_invariant [MeasurableSpace SL(2, ℝ)] [BorelSpace SL(2, ℝ)]
    (μ : Measure SL(2, ℝ)) [IsHaarMeasure μ] [InnerRegular μ] : IsMulRightInvariant μ := by
  refine ⟨fun g => ?_⟩
  rw [map_right_mul_eq_modularCharacterFun_smul, sl2R_modularCharacter_eq_one, one_smul]

theorem sl2R_canonical_haar_right_invariant [MeasurableSpace SL(2, ℝ)]
    [BorelSpace SL(2, ℝ)] : IsMulRightInvariant (haar (G := SL(2, ℝ))) :=
  sl2R_haar_right_invariant _

end TakhtajanTeo
