import TakhtajanTeo.Ch1.ComponentBlowupNormalization
import TakhtajanTeo.Ch1.ComponentTB

open Complex Set Metric Filter Topology
open scoped ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem cbs_domain_open (a : ℂ) : IsOpen (cbl_source a ⁻¹' unitDisc) := by
  apply isOpen_ball.preimage
  unfold cbl_source
  fun_prop

theorem cbs_normalized_holomorphic {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    (e : ℂ ≃ₜ ℂ) (he : EqOn e (fsans μ) unitDisc) {a : ℂ}
    (ha0 : 0 < ‖a‖) (ha1 : ‖a‖ < 1) :
    DifferentiableOn ℂ (cbl_normalized e a) (cbl_source a ⁻¹' unitDisc) := by
  have hs := (cbl_source_conformal ha0 ha1).1.mono (subset_univ (cbl_source a ⁻¹' unitDisc))
  have hf := ((S2C.s2c_conf_f hμ).1.comp hs (fun _ ht => ht)).sub_const (fsans μ a)
  apply (hf.div_const (fsans μ (cbl_source a 1) - fsans μ a)).congr
  intro t ht
  exact cbl_normalized_interior e he ha0 ha1 ht

theorem cbs_normalized_injective (e : ℂ ≃ₜ ℂ) {a : ℂ}
    (ha0 : 0 < ‖a‖) (ha1 : ‖a‖ < 1) : Function.Injective (cbl_normalized e a) := by
  intro x y hxy
  have hd := cbl_image_difference_ne_zero e ha0 ha1
  have hs : cbl_source a x = cbl_source a y := by
    apply e.injective
    have hh := congrArg (fun u : ℂ => u+e a) ((div_left_inj' hd).mp hxy)
    simpa only [sub_add_cancel] using hh
  exact (cbl_source_conformal ha0 ha1).2.1 (mem_univ x) (mem_univ y) hs

theorem cbs_normalized_deriv_ne_zero {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    (e : ℂ ≃ₜ ℂ) (he : EqOn e (fsans μ) unitDisc) {a t : ℂ}
    (ha0 : 0 < ‖a‖) (ha1 : ‖a‖ < 1) (ht : cbl_source a t ∈ unitDisc) :
    deriv (cbl_normalized e a) t ≠ 0 :=
  deriv_ne_zero_of_injOn (cbs_domain_open a) (cbs_normalized_holomorphic hμ e he ha0 ha1)
    (cbs_normalized_injective e ha0 ha1).injOn ht

/-- Exact holomorphic Schwarzian transformation for nondegenerate affine
input and output maps, proved by the actual chain rule. -/
theorem cbs_affine_schwarzian {f : ℂ → ℂ} {a α b c z : ℂ}
    (hα : α ≠ 0) (hb : b ≠ 0) (hf : AnalyticAt ℂ f (a+α*z))
    (hf' : deriv f (a+α*z) ≠ 0) :
    schwarzianHol (fun t => (f (a+α*t)-c)/b) z =
      α^2 * schwarzianHol f (a+α*z) := by
  have hg : AnalyticAt ℂ (fun t : ℂ => a+α*t) z := by fun_prop
  have hgd : deriv (fun t : ℂ => a+α*t) z = α := by simp
  have hcomp : AnalyticAt ℂ (fun t => f (a+α*t)) z :=
    AnalyticAt.comp (f := fun t : ℂ => a+α*t) (g := f) hf hg
  have hcomp' : deriv (fun t => f (a+α*t)) z ≠ 0 := by
    have hd := deriv_comp z hf.differentiableAt hg.differentiableAt
    simp only [Function.comp_def, hgd] at hd
    rw [hd]
    exact mul_ne_zero hf' hα
  have hpost := schwarzian_mobius_comp_of_ne hcomp hcomp'
    (a := 1) (b := -c) (c := 0) (d := b) (by simpa using hb) (by simpa using hb)
  simp only [one_mul, zero_mul, zero_add, ← sub_eq_add_neg] at hpost
  have hn : AnalyticAt ℂ (fun t => (f (a+α*t)-c)/b) z := (hcomp.sub analyticAt_const).div_const
  rw [schwarzian_of_analyticAt hn, schwarzian_of_analyticAt hcomp] at hpost
  have hchain := eq19_1_chain_rule hg (by simpa only [hgd] using hα) hf hf'
  simp only [Function.comp_def] at hchain
  rw [schwarzian_of_analyticAt hcomp, schwarzian_of_analyticAt hf,
    schwarzian_of_analyticAt hg, hgd] at hchain
  have hzero : schwarzianHol (fun t : ℂ => a+α*t) z = 0 := by simp [schwarzianHol]
  rw [hzero, add_zero] at hchain
  rw [hpost, hchain, mul_comm]

/-- A global QC extension is used only through its actual interior germ. -/
theorem cbs_normalized_schwarzian {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    (e : ℂ ≃ₜ ℂ) (he : EqOn e (fsans μ) unitDisc) {a t : ℂ}
    (ha0 : 0 < ‖a‖) (ha1 : ‖a‖ < 1) (ht : cbl_source a t ∈ unitDisc) :
    schwarzianHol (cbl_normalized e a) t =
      (cbl_scale a)^2 * schwarzianHol (fsans μ) (cbl_source a t) := by
  have hgerm : cbl_normalized e a =ᶠ[𝓝 t]
      (fun s => (fsans μ (cbl_source a s)-fsans μ a) /
        (fsans μ (cbl_source a 1)-fsans μ a)) := by
    filter_upwards [(cbs_domain_open a).mem_nhds ht] with s hs
    exact cbl_normalized_interior e he ha0 ha1 hs
  rw [schwarzianHol_congr hgerm]
  have hf := S2C.s2c_conf_f hμ
  exact cbs_affine_schwarzian (cbl_scale_ne_zero ha0 ha1)
    (cbl_interior_difference_ne_zero e he ha0 ha1)
    (hf.1.analyticAt (isOpen_ball.mem_nhds ht))
    (deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 ht)

/-- The exact synchronized scaling identity for the ACTUAL Bers difference. -/
theorem cbs_schwarzian_difference {μ ν : LinfStar}
    (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall)
    (eμ eν : ℂ ≃ₜ ℂ) (heμ : EqOn eμ (fsans μ) unitDisc)
    (heν : EqOn eν (fsans ν) unitDisc) {a t : ℂ}
    (ha0 : 0 < ‖a‖) (ha1 : ‖a‖ < 1) (ht : cbl_source a t ∈ unitDisc) :
    schwarzianHol (cbl_normalized eν a) t - schwarzianHol (cbl_normalized eμ a) t =
      (cbl_scale a)^2 * AInf.toFun (bersPhi ν - bersPhi μ) (cbl_source a t) := by
  rw [cbs_normalized_schwarzian hν eν heν ha0 ha1 ht,
    cbs_normalized_schwarzian hμ eμ heμ ha0 ha1 ht,
    ctb_toFun_sub, Pi.sub_apply, (bersPhi_spec hν).1 _ ht,
    (bersPhi_spec hμ).1 _ ht, ← S2C.s2c_fsans_eq hν, ← S2C.s2c_fsans_eq hμ]
  ring

#print axioms cbs_domain_open
#print axioms cbs_normalized_holomorphic
#print axioms cbs_normalized_injective
#print axioms cbs_normalized_deriv_ne_zero
#print axioms cbs_affine_schwarzian
#print axioms cbs_normalized_schwarzian
#print axioms cbs_schwarzian_difference
end TakhtajanTeo
