import TakhtajanTeo.Ch1.TCurveClosure
import Mathlib.Analysis.InnerProductSpace.Dual

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- A separating family of evaluations gives a dense span of Riesz vectors. -/
theorem tcg_eval_vectors_dense {H I : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (ev : I → H →L[ℂ] ℂ)
    (hsep : ∀ f : H, (∀ i, ev i f = 0) → f = 0) :
    Dense ((Submodule.span ℂ (range (fun i => (InnerProductSpace.toDual ℂ H).symm (ev i)))) : Set H) := by
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  apply Submodule.orthogonal_eq_bot_iff.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro f hf
  apply hsep f
  intro i
  rw [← InnerProductSpace.toDual_symm_apply]
  exact Submodule.inner_right_of_mem_orthogonal
    (subset_closure (Submodule.subset_span (mem_range_self i))) hf

/-- Weak continuity of the inverse unitary action on separating evaluations
implies strong joint continuity. Density is used only after proving norm
continuity on the Riesz vectors. -/
theorem tcg_unitary_joint_continuous {H I X : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [TopologicalSpace X]
    (ev : I → H →L[ℂ] ℂ) (hsep : ∀ f : H, (∀ i, ev i f = 0) → f = 0)
    (U : X → H ≃ₗᵢ[ℂ] H)
    (hweak : ∀ i f, Continuous (fun x => ev i ((U x).symm f))) :
    Continuous (fun p : H × X => U p.2 p.1) := by
  let k : I → H := fun i => (InnerProductSpace.toDual ℂ H).symm (ev i)
  have hk : ∀ i, Continuous (fun x => U x (k i)) := by
    intro i
    rw [continuous_iff_continuousAt]
    intro x₀
    have hinner : ∀ x, inner ℂ (U x (k i)) (U x₀ (k i)) =
        ev i ((U x).symm (U x₀ (k i))) := by
      intro x
      rw [(U x).inner_map_eq_flip]
      exact InnerProductSpace.toDual_symm_apply (x := (U x).symm (U x₀ (k i))) (y := ev i)
    have heq : (fun x => ‖U x (k i) - U x₀ (k i)‖) =
        (fun x => Real.sqrt (‖k i‖ ^ 2 -
          2 * (ev i ((U x).symm (U x₀ (k i)))).re + ‖k i‖ ^ 2)) := by
      funext x
      rw [← Real.sqrt_sq (norm_nonneg (U x (k i) - U x₀ (k i))),
        norm_sub_sq (𝕜 := ℂ), (U x).norm_map, (U x₀).norm_map, hinner]
      rfl
    have hc : Continuous (fun x => ‖U x (k i) - U x₀ (k i)‖) := by
      rw [heq]
      exact Real.continuous_sqrt.comp
        ((continuous_const.sub (continuous_const.mul (Complex.continuous_re.comp (hweak i _)))).add continuous_const)
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [sub_self, norm_zero] using hc.tendsto x₀
  apply continuous_prod_of_dense_continuous_lipschitzWith _ 1
    (tcg_eval_vectors_dense ev hsep)
  · intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨i, rfl⟩ := hf
      exact hk i
    | zero => simpa only [map_zero] using (continuous_const : Continuous (fun _ : X => (0 : H)))
    | add f g hf hg ihf ihg =>
      simp only [map_add]
      exact (continuous_add : Continuous (fun p : H × H => p.1 + p.2)).comp (ihf.prodMk ihg)
    | smul c f hf ih =>
      simp only [map_smul]
      exact (continuous_const_smul c).comp ih
  · intro x
    exact (U x).isometry.lipschitzWith

/-- Genuine A2 pullback is a linear isometry, constructed from the actual
holomorphic representatives and exact weighted norm formula. -/
theorem tcg_pullback_isometry {S : ℂ → ℂ} (hS : IsConformalOnto S unitDisc unitDisc) :
    ∃ L : A2 unitDisc →ₗᵢ[ℂ] A2 unitDisc, ∀ f : A2 unitDisc,
      EqOn (A2.toFun (L f)) (fun z => A2.toFun f (S z) * deriv S z ^ 2) unitDisc := by
  have hc : ∀ z ∈ unitDisc, ‖z‖ ≠ 1 := fun z hz => (mem_ball_zero_iff.mp hz).ne
  let F : A2 unitDisc → A2 unitDisc := fun f =>
    toA2 unitDisc (fun z => A2.toFun f (S z) * deriv S z ^ 2)
  have hs : ∀ f : A2 unitDisc, EqOn (A2.toFun (F f))
      (fun z => A2.toFun f (S z) * deriv S z ^ 2) unitDisc :=
    fun f => toA2_spec isOpen_ball hc (tcg_A2fun_pullback hS (A2.toFun_mem f))
  have ha : ∀ f g, F (f + g) = F f + F g := by
    intro f g
    apply A2.ext_of_toFun_eqOn (D := unitDisc) isOpen_ball.measurableSet
    intro z hz
    rw [hs (f + g) hz]
    dsimp only
    rw [A2.toFun_add (D := unitDisc) isOpen_ball hc (F f) (F g) hz]
    dsimp only [Pi.add_apply]
    rw [hs f hz, hs g hz, A2.toFun_add (D := unitDisc) isOpen_ball hc f g (hS.mapsTo hz)]
    simp only [Pi.add_apply]
    ring
  have hm : ∀ (c : ℂ) f, F (c • f) = c • F f := by
    intro c f
    apply A2.ext_of_toFun_eqOn (D := unitDisc) isOpen_ball.measurableSet
    intro z hz
    rw [hs (c • f) hz]
    dsimp only
    rw [A2.toFun_smul (D := unitDisc) isOpen_ball hc c (F f) hz]
    dsimp only [Pi.smul_apply]
    rw [hs f hz, A2.toFun_smul (D := unitDisc) isOpen_ball hc c f (hS.mapsTo hz)]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hn : ∀ f, ‖F f‖ = ‖f‖ := by
    intro f
    have hn' : (‖F f‖₊ : ℝ≥0∞) = (‖f‖₊ : ℝ≥0∞) :=
      (A2.norm_toFun (F f)).symm.trans
        ((normA2_congr isOpen_ball.measurableSet (hs f)).trans
          ((tcg_normA2_pullback hS (A2.toFun f)).trans (A2.norm_toFun f)))
    simpa using congrArg ENNReal.toReal hn'
  exact ⟨{ toLinearMap := { toFun := F, map_add' := ha, map_smul' := hm }, norm_map' := hn }, hs⟩

/-- Mutually inverse disk automorphisms give mutually inverse pullbacks. -/
theorem tcg_pullback_inverse {S T : ℂ → ℂ}
    (hS : IsConformalOnto S unitDisc unitDisc) (hT : IsConformalOnto T unitDisc unitDisc)
    (hST : ∀ z ∈ unitDisc, S (T z) = z)
    (L M : A2 unitDisc →ₗᵢ[ℂ] A2 unitDisc)
    (hL : ∀ f : A2 unitDisc, EqOn (A2.toFun (L f))
      (fun z => A2.toFun f (S z) * deriv S z ^ 2) unitDisc)
    (hM : ∀ f : A2 unitDisc, EqOn (A2.toFun (M f))
      (fun z => A2.toFun f (T z) * deriv T z ^ 2) unitDisc) :
    ∀ f, M (L f) = f := by
  intro f
  apply A2.ext_of_toFun_eqOn (D := unitDisc) isOpen_ball.measurableSet
  intro z hz
  rw [hM (L f) hz]
  dsimp only
  rw [hL f (hT.mapsTo hz)]
  dsimp only
  rw [hST z hz]
  have hg : S ∘ T =ᶠ[𝓝 z] id :=
    Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz) (fun w hw => hST w hw)
  have hd : deriv S (T z) * deriv T z = 1 := by
    rw [← deriv_comp z (hS.1.differentiableAt (isOpen_ball.mem_nhds (hT.mapsTo hz)))
      (hT.1.differentiableAt (isOpen_ball.mem_nhds hz)), hg.deriv_eq]
    simp
  calc
    A2.toFun f z * deriv S (T z) ^ 2 * deriv T z ^ 2 =
        A2.toFun f z * (deriv S (T z) * deriv T z) ^ 2 := by ring
    _ = A2.toFun f z := by rw [hd]; simp

/-- Bundled unitary pullback and its inverse, retaining both pointwise formulas. -/
theorem tcg_pullback_equiv {S T : ℂ → ℂ}
    (hS : IsConformalOnto S unitDisc unitDisc) (hT : IsConformalOnto T unitDisc unitDisc)
    (hST : ∀ z ∈ unitDisc, S (T z) = z) (hTS : ∀ z ∈ unitDisc, T (S z) = z) :
    ∃ U : A2 unitDisc ≃ₗᵢ[ℂ] A2 unitDisc,
      (∀ f, EqOn (A2.toFun (U f)) (fun z => A2.toFun f (S z) * deriv S z ^ 2) unitDisc) ∧
      (∀ f, EqOn (A2.toFun (U.symm f)) (fun z => A2.toFun f (T z) * deriv T z ^ 2) unitDisc) := by
  obtain ⟨L, hL⟩ := tcg_pullback_isometry hS
  obtain ⟨M, hM⟩ := tcg_pullback_isometry hT
  have hLM : L.toLinearMap.comp M.toLinearMap = LinearMap.id :=
    LinearMap.ext (tcg_pullback_inverse hT hS hTS M L hM hL)
  have hML : M.toLinearMap.comp L.toLinearMap = LinearMap.id :=
    LinearMap.ext (tcg_pullback_inverse hS hT hST L M hL hM)
  exact ⟨LinearIsometryEquiv.ofLinearIsometry L M.toLinearMap hLM hML, hL, hM⟩

/-- Point evaluations on A2 are genuine continuous linear functionals. -/
theorem tcg_A2_evaluations :
    ∃ ev : unitDisc → A2 unitDisc →L[ℂ] ℂ,
      ∀ z f, ev z f = A2.toFun f z := by
  choose ev hev using (fun z : unitDisc => ctb_ev z.2)
  refine ⟨fun z => (ev z).comp A2toAInfCLM, ?_⟩
  intro z f
  change ev z (A2toAInf f) = _
  rw [hev]
  exact (A2toAInf_bounded.2 f).2 z z.2

/-- Strong joint continuity of the actual A2 pullback for a family of disk
automorphisms. Only the inverse maps and their first derivatives are
assumed pointwise continuous in the parameter. -/
theorem tcg_disk_pullback_joint_continuous {X : Type*} [TopologicalSpace X]
    (S T : X → ℂ → ℂ)
    (hS : ∀ x, IsConformalOnto (S x) unitDisc unitDisc)
    (hT : ∀ x, IsConformalOnto (T x) unitDisc unitDisc)
    (hST : ∀ x z, z ∈ unitDisc → S x (T x z) = z)
    (hTS : ∀ x z, z ∈ unitDisc → T x (S x z) = z)
    (hTv : ∀ z ∈ unitDisc, Continuous (fun x => T x z))
    (hTd : ∀ z ∈ unitDisc, Continuous (fun x => deriv (T x) z)) :
    Continuous (fun p : A2 unitDisc × X =>
      toA2 unitDisc (fun z => A2.toFun p.1 (S p.2 z) * deriv (S p.2) z ^ 2)) := by
  choose U hU hUi using (fun x => tcg_pullback_equiv (hS x) (hT x) (hST x) (hTS x))
  obtain ⟨ev, hev⟩ := tcg_A2_evaluations
  have hsep : ∀ f : A2 unitDisc, (∀ z, ev z f = 0) → f = 0 := by
    intro f hf
    apply A2.ext_of_toFun_eqOn (D := unitDisc) isOpen_ball.measurableSet
    intro z hz
    rw [← hev ⟨z, hz⟩ f, ← hev ⟨z, hz⟩ 0, hf, map_zero]
  have hw : ∀ z f, Continuous (fun x => ev z ((U x).symm f)) := by
    intro z f
    have heq : (fun x => ev z ((U x).symm f)) =
        (fun x => A2.toFun f (T x z) * deriv (T x) z ^ 2) := by
      funext x
      rw [hev]
      exact hUi x f z.2
    rw [heq]
    exact ((A2.toFun_spec f).1.continuousOn.comp_continuous (hTv z z.2)
      (fun x => (hT x).mapsTo z.2)).mul ((hTd z z.2).pow 2)
  have hcont := tcg_unitary_joint_continuous ev hsep U hw
  have heq : (fun p : A2 unitDisc × X =>
      toA2 unitDisc (fun z => A2.toFun p.1 (S p.2 z) * deriv (S p.2) z ^ 2)) =
      (fun p => U p.2 p.1) := by
    funext p
    apply A2.ext_of_toFun_eqOn (D := unitDisc) isOpen_ball.measurableSet
    intro z hz
    have hs := toA2_spec (D := unitDisc) isOpen_ball
      (fun w hw => (mem_ball_zero_iff.mp hw).ne) (tcg_A2fun_pullback (hS p.2) (A2.toFun_mem p.1))
    exact (hs hz).trans (hU p.2 p.1 hz).symm
  rw [heq]
  exact hcont

/-- The concrete disk Mobius family, with arbitrary continuous rotation
and disk parameters, acts jointly strongly continuously on A2. -/
theorem tcg_mobius_pullback_continuous {X : Type*} [TopologicalSpace X]
    (c a : X → ℂ) (hcc : Continuous c) (hac : Continuous a)
    (hc : ∀ x, ‖c x‖ = 1) (ha : ∀ x, ‖a x‖ < 1) :
    let S : X → ℂ → ℂ := fun x z => blaschke (-a x) (conj (c x) * z)
    Continuous (fun p : A2 unitDisc × X =>
      toA2 unitDisc (fun z => A2.toFun p.1 (S p.2 z) * deriv (S p.2) z ^ 2)) := by
  let S : X → ℂ → ℂ := fun x z => blaschke (-a x) (conj (c x) * z)
  let T : X → ℂ → ℂ := fun x z => c x * blaschke (a x) z
  have hS : ∀ x, IsConformalOnto (S x) unitDisc unitDisc := by
    intro x
    exact (isConformalOnto_blaschke (by simpa only [norm_neg] using ha x)).comp
      (isConformalOnto_rot (by simpa only [norm_conj] using hc x))
  have hT : ∀ x, IsConformalOnto (T x) unitDisc unitDisc :=
    fun x => (isConformalOnto_rot (hc x)).comp (isConformalOnto_blaschke (ha x))
  have hcc1 : ∀ x, c x * conj (c x) = 1 := by
    intro x
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]
    norm_num
  have hST : ∀ x z, z ∈ unitDisc → S x (T x z) = z := by
    intro x z hz
    dsimp [S, T]
    rw [← mul_assoc, mul_comm (conj (c x)), hcc1, one_mul]
    exact blaschke_neg_blaschke (ha x) (mem_ball_zero_iff.mp hz)
  have hTS : ∀ x z, z ∈ unitDisc → T x (S x z) = z := by
    intro x z hz
    have hcz : ‖conj (c x) * z‖ < 1 := by
      simpa only [norm_mul, norm_conj, hc, one_mul] using mem_ball_zero_iff.mp hz
    have hb := blaschke_neg_blaschke (a := -a x)
      (by simpa only [norm_neg] using ha x) hcz
    dsimp [S, T]
    rw [neg_neg] at hb
    rw [hb, ← mul_assoc, hcc1, one_mul]
  have hTv : ∀ z ∈ unitDisc, Continuous (fun x => T x z) := by
    intro z hz
    exact hcc.mul ((continuous_const.sub hac).div
      (continuous_const.sub ((Complex.continuous_conj.comp hac).mul_const z))
      (fun x => blaschke_den_ne_zero (ha x) (mem_ball_zero_iff.mp hz)))
  have hTd : ∀ z ∈ unitDisc, Continuous (fun x => deriv (T x) z) := by
    intro z hz
    have heq : (fun x => deriv (T x) z) =
        (fun x => c x * ((1 - a x * conj (a x)) / (1 - conj (a x) * z) ^ 2)) := by
      funext x
      exact ((hasDerivAt_blaschke (ha x) (mem_ball_zero_iff.mp hz)).const_mul (c x)).deriv
    rw [heq]
    exact hcc.mul ((continuous_const.sub (hac.mul (Complex.continuous_conj.comp hac))).div
      ((continuous_const.sub ((Complex.continuous_conj.comp hac).mul_const z)).pow 2)
      (fun x => pow_ne_zero 2 (blaschke_den_ne_zero (ha x) (mem_ball_zero_iff.mp hz))))
  exact tcg_disk_pullback_joint_continuous S T hS hT hST hTS hTv hTd

#print axioms tcg_eval_vectors_dense
#print axioms tcg_unitary_joint_continuous
#print axioms tcg_pullback_equiv
#print axioms tcg_disk_pullback_joint_continuous
#print axioms tcg_mobius_pullback_continuous
end TakhtajanTeo
