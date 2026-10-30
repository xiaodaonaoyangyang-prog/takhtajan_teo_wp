import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import TakhtajanTeo.Ch1.BanachHolomorphic

open Set Filter Topology

noncomputable section
namespace TakhtajanTeo

-- L1
/-- A locally injective strict submersion with complemented kernel has injective derivative. -/
theorem his_injective_of_complemented
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    {f : E → F} {A : E →L[𝕜] F} {a : E} {s : Set E}
    (hf : HasStrictFDerivAt f A a) (hA : Function.Surjective A)
    (hker : A.ker.ClosedComplemented) (hs : s ∈ 𝓝 a) (hinj : Set.InjOn f s) :
    Function.Injective A := by
  have hr : A.range = ⊤ := LinearMap.range_eq_top.mpr hA
  let g : A.ker → E := hf.implicitFunctionOfComplemented f A hr hker (f a)
  have hg0 : g 0 = a := hf.implicitFunctionOfComplemented_apply_image hr hker
  have hgd : HasStrictFDerivAt g A.ker.subtypeL 0 :=
    hf.to_implicitFunctionOfComplemented hr hker
  have hgs : ∀ᶠ z in 𝓝 (0 : A.ker), g z ∈ s := by
    apply hgd.continuousAt.preimage_mem_nhds
    rwa [hg0]
  have hfg : ∀ᶠ z in 𝓝 (0 : A.ker), f (g z) = f a := by
    have ht : Tendsto (fun z : A.ker => (f a, z)) (𝓝 0) (𝓝 (f a, 0)) :=
      tendsto_const_nhds.prodMk_nhds tendsto_id
    exact ht.eventually (hf.map_implicitFunctionOfComplemented_eq hr hker)
  have hconst : g =ᶠ[𝓝 (0 : A.ker)] fun _ => a := by
    filter_upwards [hgs, hfg] with z hz heq
    exact hinj hz (mem_of_mem_nhds hs) heq
  -- The implicit fiber has derivative equal to the kernel embedding. Thus a nonzero
  -- kernel cannot give a locally constant fiber, as local injectivity would require.
  have hzero : A.ker.subtypeL = (0 : A.ker →L[𝕜] E) :=
    hgd.hasFDerivAt.unique ((hasFDerivAt_const a (0 : A.ker)).congr_of_eventuallyEq hconst)
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro v hv
  have hz := DFunLike.congr_fun hzero (⟨v, hv⟩ : A.ker)
  simpa only [Submodule.mem_bot, Submodule.coe_subtypeL, Submodule.coe_subtype,
    zero_apply] using hz

-- L2
/-- On a Hilbert domain, local injectivity and a surjective strict derivative force a zero kernel. -/
theorem his_injective_of_surjective
    {𝕜 : Type*} [RCLike 𝕜]
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    {f : E → F} {A : E →L[𝕜] F} {a : E} {s : Set E}
    (hf : HasStrictFDerivAt f A a) (hA : Function.Surjective A)
    (hs : s ∈ 𝓝 a) (hinj : Set.InjOn f s) : Function.Injective A := by
  exact his_injective_of_complemented hf hA
    ⟨A.ker.orthogonalProjectionOnto, A.ker.orthogonalProjectionOnto_mem_subspace_eq_self⟩ hs hinj

-- L3
/-- Holomorphic version for locally injective charts with an actual surjective derivative. -/
theorem his_holomorphic_injective_of_surjective
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {f : E → F} {U : Set E} {a : E}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (ha : a ∈ U)
    (hinj : Set.InjOn f U) (hA : Function.Surjective (fderiv ℂ f a)) :
    Function.Injective (fderiv ℂ f a) := by
  exact his_injective_of_surjective (bh_hasStrictFDerivAt hU hf ha) hA (hU.mem_nhds ha) hinj

end TakhtajanTeo
