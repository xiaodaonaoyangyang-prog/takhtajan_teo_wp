import TakhtajanTeo.Ch1.GroupChain2
import TakhtajanTeo.Ch1.GroupB1
import TakhtajanTeo.Ch1.GroupDiscEstimate

/-!
# Conditional assembly of the guarded Lemma 2.5 proposition

Origin C1 regularity (S1) and the base-point limit (S3) remain explicit hypotheses.
The verified S4 disk interface is combined with exterior regularity, reflection,
and inversion. One common radius is chosen with a margin for `3η + 4δ`.
No appeal to the original `lemma_2_5` is made, and that original remains held.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- Extend the supplied disk C1 estimate to every finite point off the unit circle. -/
theorem grp25a_regular_all {δ : ℝ} (hδ : δ<1)
    (hD : ∀ μ∈harmonicBeltrami, ‖μ‖<δ → ∀ z∈unitDisc, ContDiffAt ℝ 1 (wA μ) z) :
    ∀ μ∈harmonicBeltrami, ‖μ‖<δ → ∀ z : ℂ, z∈unitDisc∪unitDiscExterior →
      wAS μ (z : ExtPlane)≠extInf → ContDiffAt ℝ 1 (wA μ) z := by
  intro μ hμ hμδ z hz hp
  rcases hz with hz|hz
  · exact hD μ hμ hμδ z hz
  · exact (grp25_regular_ext hμ (hμδ.trans hδ) hz hp).1

/-- Reflection and inversion assemble the exact guarded original proposition at the same δ. -/
theorem grp25a_assemble {ε η δ : ℝ} (hη0 : 0<η) (hη1 : η<1/4)
    (hδ0 : 0<δ) (hδ1 : δ<1/4) (hηε : η≤ε) (hbudget : 3*η+4*δ≤ε)
    (hD : ∀ μ∈harmonicBeltrami, ‖μ‖<δ → ∀ z∈unitDisc,
      ContDiffAt ℝ 1 (wA μ) z ∧
      |‖dz (wA μ) z‖^2/(1-‖wA μ z‖^2)^2-1/(1-‖z‖^2)^2|<η/(1-‖z‖^2)^2) :
    Lemma25Prop ε δ := by
  have hδlt : δ<1 := by linarith
  have hreg := grp25a_regular_all hδlt (fun μ hμ hμδ z hz => (hD μ hμ hμδ z hz).1)
  have hE := grp25_reflect hδlt (fun μ hμ hμδ z hz =>
    ⟨(hD μ hμ hμδ z hz).1.differentiableAt (by norm_num),(hD μ hμ hμδ z hz).2⟩)
  have hall : ∀ μ∈harmonicBeltrami, ‖μ‖<δ → ∀ z : ℂ, z∈unitDisc∪unitDiscExterior →
      wAS μ (z : ExtPlane)≠extInf →
      |‖dz (wA μ) z‖^2/(1-‖wA μ z‖^2)^2-1/(1-‖z‖^2)^2|<η/(1-‖z‖^2)^2 := by
    intro μ hμ hμδ z hz hp
    rcases hz with hz|hz
    · exact (hD μ hμ hμδ z hz).2
    · exact hE μ hμ hμδ z hz hp
  have hinv := grp25_inv hη0 hη1 hδ0 hδ1 hreg hall
  refine ⟨hδ0,hδlt,?_⟩
  intro μ hμ hμδ z hz
  constructor
  · intro hp
    exact (hall μ hμ hμδ z hz hp).trans_le (div_le_div_of_nonneg_right hηε (sq_nonneg _))
  · intro hp
    exact (hinv μ hμ hμδ z hz hp).trans_le (div_le_div_of_nonneg_right hbudget (sq_nonneg _))

/-- Parameter selection leaves a margin for the `3η+4δ` error produced by inversion. -/
theorem grp25a_parameters {ε d : ℝ} (hε : 0<ε) (hd : 0<d) :
    let η := min (ε/8) (1/8)
    let δ := min d (η/8)
    0<η ∧ η<1/4 ∧ 0<δ ∧ δ<1/4 ∧ δ≤d ∧ η≤ε ∧ 3*η+4*δ≤ε := by
  dsimp only
  have hη : 0 < min (ε/8) (1/8) := lt_min (by positivity) (by norm_num)
  have hηε := min_le_left (ε/8) (1/8)
  have hη1 := min_le_right (ε/8) (1/8)
  have hδ : 0 < min d (min (ε/8) (1/8)/8) := lt_min hd (by positivity)
  have hδd := min_le_left d (min (ε/8) (1/8)/8)
  have hδη := min_le_right d (min (ε/8) (1/8)/8)
  exact ⟨hη,by linarith,hδ,by linarith,hδd,by linarith,by linarith⟩

/-- Conditional assembly only: the origin regularity and base-point limit remain explicit inputs. -/
theorem grp25a_lemma_2_5_of_origin
    (hreg0 : ∀ μ∈harmonicBeltrami, ‖μ‖<1 → ContDiffAt ℝ 1 (wA μ) 0)
    (hbase : ∀ ε>0, ∃ δ>0, ∀ μ∈harmonicBeltrami, ‖μ‖<δ →
      |‖dz (wA μ) 0‖^2/(1-‖wA μ 0‖^2)^2-1|<ε) :
    ∀ ε>0, ∃ δ, Lemma25Prop ε δ := by
  intro ε hε
  let η : ℝ := min (ε/8) (1/8)
  have hη0 : 0<η := lt_min (by positivity) (by norm_num)
  obtain ⟨d,hd,hbd⟩ := hbase η hη0
  let δ : ℝ := min d (η/8)
  obtain ⟨_,hη1,hδ0,hδ1,hδd,hηε,hbudget⟩ := grp25a_parameters hε hd
  have hδlt : δ<1 := lt_trans hδ1 (by norm_num)
  have hD := grp25_disc_of_origin hδlt.le
    (fun μ hμ hμδ => hreg0 μ hμ (hμδ.trans hδlt))
    (fun μ hμ hμδ => hbd μ hμ (hμδ.trans_le hδd))
  exact ⟨δ,grp25a_assemble hη0 hη1 hδ0 hδ1 hηε hbudget hD⟩

end TakhtajanTeo
