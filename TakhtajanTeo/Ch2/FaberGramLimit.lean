import TakhtajanTeo.Ch2.FaberGramEnergy
import TakhtajanTeo.Ch2.FaberGramIntegral

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo.Ch2
open LiZhongQC

/-- The unweighted coefficient energy is genuinely summable. -/
theorem faber_grunsky_energy_summable {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f unitDisc) (hi : InjOn f unitDisc) (hf0 : f 0=0)
    {a : ℕ → ℕ → ℂ} {b00 : ℂ}
    (hexp : ∀ z∈unitDisc, ∀ w∈unitDisc, z≠w → ∃ S : ℂ,
      HasSum (fun p : ℕ × ℕ => a p.1 p.2*z^p.1*w^p.2) S ∧ (f z-f w)/(z-w)=exp (b00-S))
    (N : ℕ) (μ : ℕ → ℂ) :
    Summable (fun p : ℕ => ((p+1 : ℕ) : ℝ)*
      ‖∑ k∈Finset.Icc 1 N, (k : ℂ)*μ k*a (p+1) k‖^2) := by
  let c : ℕ → ℝ := fun p => ((p+1 : ℕ) : ℝ)*
    ‖∑ k∈Finset.Icc 1 N, (k : ℂ)*μ k*a (p+1) k‖^2
  have hc (p : ℕ) : 0≤c p := by dsimp [c]; positivity
  apply summable_of_sum_range_le hc (c := ∑ k∈Finset.Icc 1 N, (k : ℝ)*‖μ k‖^2)
  intro P
  have hL : Tendsto (fun ρ : ℝ => ∑ p∈Finset.range P, c p*ρ^(2*(p+1)))
      (𝓝[<] 1) (𝓝 (∑ p∈Finset.range P, c p)) := by
    have hh : Continuous (fun ρ : ℝ => ∑ p∈Finset.range P, c p*ρ^(2*(p+1))) := by fun_prop
    exact tendsto_nhdsWithin_of_tendsto_nhds (by simpa using hh.tendsto 1)
  have hR : Tendsto (fun ρ : ℝ => ∑ k∈Finset.Icc 1 N, (k : ℝ)*‖μ k‖^2*(ρ^(2*k))⁻¹)
      (𝓝[<] 1) (𝓝 (∑ k∈Finset.Icc 1 N, (k : ℝ)*‖μ k‖^2)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    refine tendsto_finset_sum _ (fun k _ => ?_)
    have hh : ContinuousAt (fun ρ : ℝ => (ρ^(2*k))⁻¹) 1 :=
      ContinuousAt.inv₀ (by fun_prop) (by simp)
    simpa using hh.tendsto.const_mul ((k : ℝ)*‖μ k‖^2)
  apply le_of_tendsto_of_tendsto hL hR
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ)<1 by norm_num)] with ρ hρ
  obtain ⟨hs,hle⟩ := g2_grunsky_finite hf hi hf0 hexp hρ.1 hρ.2 N μ
  exact (hs.sum_le_tsum (Finset.range P) (fun p _ => mul_nonneg (hc p)
    (pow_nonneg hρ.1.le _))).trans hle

theorem faber_energy_tsum_tendsto {c : ℕ → ℝ} (hc : Summable c) (hn : ∀ n, 0≤c n) :
    Tendsto (fun ρ : ℝ => ∑' n, c n*ρ^(2*(n+1))) (𝓝[<] 1) (𝓝 (∑' n, c n)) := by
  apply tendsto_tsum_of_dominated_convergence hc
  · intro n
    have hh : Continuous (fun ρ : ℝ => c n*ρ^(2*(n+1))) := by fun_prop
    exact tendsto_nhdsWithin_of_tendsto_nhds (by simpa using hh.tendsto 1)
  · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ)<1 by norm_num)] with ρ hρ n
    rw [Real.norm_of_nonneg (mul_nonneg (hn n) (pow_nonneg hρ.1.le _))]
    exact mul_le_of_le_one_right (hn n) (pow_le_one₀ hρ.1.le hρ.2.le)

/-- Polynomial inverse differentials have finite energy outside each interior image circle. -/
theorem faber_inverse_poly_integrable {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f unitDisc) (hi : InjOn f unitDisc) (hf0 : f 0=0)
    {ρ : ℝ} (hρ0 : 0<ρ) (hρ1 : ρ<1) (p : Polynomial ℂ) :
    IntegrableOn (fun w => ‖deriv (fun v => p.eval v⁻¹) w‖^2)
      (f '' closedBall (0 : ℂ) ρ)ᶜ := by
  have hsub : closedBall (0 : ℂ) ρ⊆unitDisc := closedBall_subset_ball hρ1
  have hc : IsCompact (f '' closedBall (0 : ℂ) ρ) :=
    (isCompact_closedBall (0 : ℂ) ρ).image_of_continuousOn (hf.continuousOn.mono hsub)
  have hopen : IsOpen (f '' ball (0 : ℂ) ρ) :=
    (RMT.differentiableOn_invFunOn_of_injOn isOpen_ball
      (hf.mono (ball_subset_ball hρ1.le)) (hi.mono (ball_subset_ball hρ1.le))).1
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds
    (show (0 : ℂ)∈f '' ball (0 : ℂ) ρ from ⟨0,mem_ball_self hρ0,hf0⟩))
  have hnorm (w : ℂ) (hw : w∈(f '' closedBall (0 : ℂ) ρ)ᶜ) : ε≤‖w‖ := by
    by_contra! hlt
    exact hw (image_mono ball_subset_closedBall (hball (mem_ball_zero_iff.mpr hlt)))
  have hne (w : ℂ) (hw : w∈(f '' closedBall (0 : ℂ) ρ)ᶜ) : w≠0 :=
    norm_pos_iff.mp (hε.trans_le (hnorm w hw))
  have hbound : (fun w : ℂ => w⁻¹) '' (f '' closedBall (0 : ℂ) ρ)ᶜ⊆closedBall (0 : ℂ) ε⁻¹ := by
    rintro _ ⟨w,hw,rfl⟩
    apply mem_closedBall_zero_iff.mpr
    rw [norm_inv]
    exact inv_anti₀ hε (hnorm w hw)
  exact a21_integrable_sq hc.isClosed.isOpen_compl.measurableSet
    (polynomial_inverse_deriv_mem_A21 hc.isClosed.isOpen_compl hne hbound p)

/-- The decreasing complements of image disks exhaust the complement of the open image. -/
theorem faber_exterior_integral_tendsto {f : ℂ → ℂ}
    (hf : ContinuousOn f unitDisc) {r : ℕ → ℝ} (hr : Monotone r)
    (hr1 : ∀ n, r n<1) (hlim : Tendsto r atTop (𝓝 1)) {F : ℂ → ℝ}
    (hF : IntegrableOn F (f '' closedBall (0 : ℂ) (r 0))ᶜ) :
    Tendsto (fun n => ∫ w in (f '' closedBall (0 : ℂ) (r n))ᶜ, F w)
      atTop (𝓝 (∫ w in (f '' unitDisc)ᶜ, F w)) := by
  have hmeas (n : ℕ) : MeasurableSet (f '' closedBall (0 : ℂ) (r n))ᶜ :=
    ((isCompact_closedBall (0 : ℂ) (r n)).image_of_continuousOn
      (hf.mono (closedBall_subset_ball (hr1 n)))).isClosed.measurableSet.compl
  have hanti : Antitone (fun n => (f '' closedBall (0 : ℂ) (r n))ᶜ) := by
    intro n m hnm
    exact compl_subset_compl.mpr (image_mono (closedBall_subset_closedBall (hr hnm)))
  have he : (⋂ n, (f '' closedBall (0 : ℂ) (r n))ᶜ)=(f '' unitDisc)ᶜ := by
    ext w
    constructor
    · intro hw hwD
      obtain ⟨z,hz,rfl⟩ := hwD
      have hz1 : ‖z‖<1 := mem_ball_zero_iff.mp hz
      obtain ⟨n,hn⟩ := (hlim.eventually (lt_mem_nhds hz1)).exists
      exact mem_iInter.mp hw n ⟨z,mem_closedBall_zero_iff.mpr hn.le,rfl⟩
    · intro hw
      apply mem_iInter.mpr
      intro n hn
      exact hw (image_mono (closedBall_subset_ball (hr1 n)) hn)
  simpa only [he] using Antitone.tendsto_setIntegral hmeas hanti hF

/-- Exact finite Grunsky energy on the complement of the whole conformal image. -/
theorem faber_grunsky_energy_limit {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f unitDisc) (hi : InjOn f unitDisc) (hf0 : f 0=0)
    {a φ : ℕ → ℕ → ℂ} {b00 : ℂ}
    (hexp : ∀ z∈unitDisc, ∀ w∈unitDisc, z≠w → ∃ S : ℂ,
      HasSum (fun p : ℕ × ℕ => a p.1 p.2*z^p.1*w^p.2) S ∧ (f z-f w)/(z-w)=exp (b00-S))
    (hφ : ∀ l k : ℕ, ∀ r : ℝ, 0<r → r<1 → Real.circleAverage (fun z => f z^l/z^k) 0 r=φ l k)
    (hφ0 : ∀ l k : ℕ, k<l → φ l k=0) (N : ℕ) (μ : ℕ → ℂ) :
    let ν : ℕ → ℂ := fun l => ∑ k∈Finset.Icc 1 N, (k : ℂ)*μ k*φ l k/(l : ℂ)
    let H : ℂ → ℂ := fun w => ∑ l∈Finset.Icc 1 N, ν l*w^(-(l : ℤ))
    Summable (fun p : ℕ => ((p+1 : ℕ) : ℝ)*
      ‖∑ k∈Finset.Icc 1 N, (k : ℂ)*μ k*a (p+1) k‖^2) ∧
    (∫ w in (f '' unitDisc)ᶜ, ‖deriv H w‖^2) =
      π*((∑ k∈Finset.Icc 1 N, (k : ℝ)*‖μ k‖^2) -
        ∑' p : ℕ, ((p+1 : ℕ) : ℝ)*‖∑ k∈Finset.Icc 1 N, (k : ℂ)*μ k*a (p+1) k‖^2) := by
  dsimp only
  let ν : ℕ → ℂ := fun l => ∑ k∈Finset.Icc 1 N, (k : ℂ)*μ k*φ l k/(l : ℂ)
  let H : ℂ → ℂ := fun w => ∑ l∈Finset.Icc 1 N, ν l*w^(-(l : ℤ))
  let c : ℕ → ℝ := fun p => ((p+1 : ℕ) : ℝ)*
    ‖∑ k∈Finset.Icc 1 N, (k : ℂ)*μ k*a (p+1) k‖^2
  have hc : Summable c := faber_grunsky_energy_summable hf hi hf0 hexp N μ
  refine ⟨hc,?_⟩
  change (∫ w in (f '' unitDisc)ᶜ, ‖deriv H w‖^2)=
    π*((∑ k∈Finset.Icc 1 N, (k : ℝ)*‖μ k‖^2)-∑' p, c p)
  let p : Polynomial ℂ := ∑ l∈Finset.Icc 1 N, Polynomial.monomial l (ν l)
  have hp : H=(fun w => p.eval w⁻¹) := by
    funext w
    simp only [H,p,Polynomial.eval_finsetSum,Polynomial.eval_monomial]
    apply Finset.sum_congr rfl
    intro l _
    rw [zpow_neg,zpow_natCast,inv_pow]
  obtain ⟨r,hr,hri,hrlim⟩ := exists_seq_strictMono_tendsto' (show (0 : ℝ)<1 by norm_num)
  have hI := faber_exterior_integral_tendsto hf.continuousOn hr.monotone
    (fun n => (hri n).2) hrlim (F := fun w => ‖deriv H w‖^2)
    (by rw [hp]; exact faber_inverse_poly_integrable hf hi hf0 (hri 0).1 (hri 0).2 p)
  have hLT : Tendsto r atTop (𝓝[<] 1) :=
    tendsto_nhdsWithin_iff.mpr ⟨hrlim,Eventually.of_forall (fun n => (hri n).2)⟩
  have hT := (faber_energy_tsum_tendsto hc (fun n => by dsimp [c]; positivity)).comp hLT
  have hN : Tendsto (fun t : ℝ => ∑ k∈Finset.Icc 1 N, (k : ℝ)*‖μ k‖^2*(t^(2*k))⁻¹)
      (𝓝 1) (𝓝 (∑ k∈Finset.Icc 1 N, (k : ℝ)*‖μ k‖^2)) := by
    refine tendsto_finset_sum _ (fun k _ => ?_)
    have hh : ContinuousAt (fun t : ℝ => (t^(2*k))⁻¹) 1 :=
      ContinuousAt.inv₀ (by fun_prop) (by simp)
    simpa using hh.tendsto.const_mul ((k : ℝ)*‖μ k‖^2)
  have hR := ((hN.comp hrlim).sub hT).const_mul π
  apply tendsto_nhds_unique hI
  apply hR.congr'
  exact Eventually.of_forall (fun n =>
    (faber_grunsky_energy_at_radius hf hi hf0 hexp hφ hφ0 (hri n).1 (hri n).2 N μ).2.symm)

/-- A null omitted set identifies the complementary restricted area measures. -/
theorem faber_complement_measure {U V : Set ℂ} (hd : Disjoint U V)
    (hnull : volume (U∪V)ᶜ=0) : volume.restrict Uᶜ=volume.restrict V := by
  apply Measure.restrict_congr_set
  have hcover : ∀ᵐ z : ℂ, z∈U∪V := by
    exact ae_iff.mpr hnull
  filter_upwards [hcover] with z hz
  apply propext
  change (z∉U)↔z∈V
  constructor
  · intro hn
    exact hz.resolve_left hn
  · intro hv hu
    exact Set.disjoint_left.mp hd hu hv

end TakhtajanTeo.Ch2
