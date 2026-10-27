module

public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.UniformSpace.HeineCantor

/-! # Function-space calculus for characteristic rectangles

Continuous state sources act on a compact supremum space. A uniform
Taylor remainder proves C¹ superposition without differentiating a
solution. Smooth localization supplies global source maps agreeing on
any prescribed compact nondegenerate state range. These are analytic
components of internal project record (46)–(47), not a rectangle existence input.
-/

public section

open Set Filter Asymptotics Function Metric
open scoped Topology NNReal

namespace EmcsfAcExtension.Local.StripFunctionSpace

variable {K E G : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Apply a continuous field of bounded linear maps pointwise in the compact supremum space. -/
@[expose] noncomputable def pointwiseCLM (A : C(K, E →L[ℝ] G)) : C(K, E) →L[ℝ] C(K, G) :=
  LinearMap.mkContinuous
    { toFun := fun h => ⟨fun t => A t (h t), A.continuous.clm_apply h.continuous⟩
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
    ‖A‖ (by
      intro h
      change ‖(⟨fun t => A t (h t), A.continuous.clm_apply h.continuous⟩ : C(K,G))‖ ≤ ‖A‖ * ‖h‖
      apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg A) (norm_nonneg h))).mpr
      intro t
      exact (A t).le_opNorm (h t) |>.trans
        (mul_le_mul (ContinuousMap.norm_coe_le_norm A t)
          (ContinuousMap.norm_coe_le_norm h t) (norm_nonneg _) (norm_nonneg _)))

/-- Pointwise application has operator norm bounded by the supremum norm of its coefficient field.
-/
lemma norm_pointwiseCLM_le (A : C(K, E →L[ℝ] G)) : ‖pointwiseCLM A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound (pointwiseCLM A) (norm_nonneg A)
  intro h
  apply (ContinuousMap.norm_le (pointwiseCLM A h) (mul_nonneg (norm_nonneg A) (norm_nonneg h))).mpr
  intro t
  exact (A t).le_opNorm (h t) |>.trans
    (mul_le_mul (ContinuousMap.norm_coe_le_norm A t)
      (ContinuousMap.norm_coe_le_norm h t) (norm_nonneg _) (norm_nonneg _))

/-- Pointwise application is Lipschitz in its coefficient field, with coefficient one. -/
lemma norm_sub_pointwiseCLM_le (A B : C(K, E →L[ℝ] G)) :
    ‖pointwiseCLM A - pointwiseCLM B‖ ≤ ‖A-B‖ := by
  have heq : pointwiseCLM A - pointwiseCLM B = pointwiseCLM (A-B) := by
    ext h t
    rfl
  rw [heq]
  exact norm_pointwiseCLM_le _

/-- The superposition map on continuous functions with compact domain. -/
@[expose] noncomputable def superposition (f : E → G) (hf : Continuous f) : C(K,E) → C(K,G) :=
  fun u => ⟨fun t => f (u t), hf.comp u.continuous⟩

/-- The pointwise state derivative of the superposition map. -/
@[expose] noncomputable def superpositionDeriv (D : E → E →L[ℝ] G) (hD : Continuous D)
    (u : C(K, E)) : C(K,E) →L[ℝ] C(K,G) :=
  pointwiseCLM ⟨fun t => D (u t), hD.comp u.continuous⟩

private lemma taylor_remainder_le_of_bound {f : E → G} {D : E → E →L[ℝ] G}
    (hf : ∀ x, HasFDerivAt f (D x) x) (x y : E) {ε : ℝ}
    (hD : ∀ z ∈ segment ℝ x y, ‖D z - D x‖ ≤ ε) :
    ‖f y - f x - D x (y-x)‖ ≤ ε * ‖y-x‖ := by
  exact (convex_segment x y).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun z _ => (hf z).hasFDerivWithinAt) hD
    (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)

omit [NormedSpace ℝ E] [NormedSpace ℝ G] in
/-- A uniformly continuous state map induces a uniformly continuous superposition map. -/
lemma uniformContinuous_superposition {f : E → G} (hf : UniformContinuous f) :
    UniformContinuous (superposition f hf.continuous (K := K)) := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := Metric.uniformContinuous_iff.mp hf ε hε
  refine ⟨δ, hδ, ?_⟩
  intro u v huv
  rw [dist_eq_norm] at huv ⊢
  apply (ContinuousMap.norm_lt_iff _ hε).mpr
  intro t
  change ‖f (u t)-f (v t)‖ < ε
  rw [← dist_eq_norm]
  exact hbound ((show dist (u t) (v t) ≤ ‖u-v‖ by
    simpa only [dist_eq_norm, ContinuousMap.sub_apply] using (u-v).norm_coe_le_norm t).trans_lt huv)

/-- Uniform continuity of the state derivative justifies differentiation in the supremum space. -/
lemma hasFDerivAt_superposition_of_uniformContinuous {f : E → G}
    {D : E → E →L[ℝ] G}
    (hf : ∀ x, HasFDerivAt f (D x) x) (hD : UniformContinuous D) (u : C(K, E)) :
    HasFDerivAt (superposition f (continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt))
      (superpositionDeriv D hD.continuous u) u := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff]
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := Metric.uniformContinuous_iff.mp hD ε hε
  filter_upwards [Metric.ball_mem_nhds (0 : C(K,E)) hδ] with h hh
  have hhδ : ‖h‖ < δ := by simpa only [Metric.mem_ball, dist_zero_right] using hh
  apply (ContinuousMap.norm_le _ (mul_nonneg hε.le (norm_nonneg h))).mpr
  intro t
  change ‖f (u t + h t) - f (u t) - D (u t) (h t)‖ ≤ ε * ‖h‖
  have hb := taylor_remainder_le_of_bound hf (u t) (u t+h t) (ε := ε) (by
    intro z hz
    apply le_of_lt
    rw [← dist_eq_norm]
    apply hbound
    rw [dist_eq_norm]
    exact ((norm_sub_le_of_mem_segment hz).trans (by
      simpa only [add_sub_cancel_left] using h.norm_coe_le_norm t)).trans_lt hhδ)
  simp only [add_sub_cancel_left] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left (h.norm_coe_le_norm t) hε.le)

/-- A continuously differentiable state map with uniformly continuous derivative acts C¹ on the
compact supremum space. -/
lemma contDiff_superposition_of_uniformContinuous {f : E → G}
    {D : E → E →L[ℝ] G}
    (hf : ∀ x, HasFDerivAt f (D x) x) (hD : UniformContinuous D) :
    ContDiff ℝ 1 (superposition f (continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt)
      (K := K)) := by
  rw [contDiff_one_iff_hasFDerivAt]
  refine ⟨superpositionDeriv D hD.continuous, ?_,
    hasFDerivAt_superposition_of_uniformContinuous hf hD⟩
  have hL : LipschitzWith 1 (pointwiseCLM (K := K) (E := E) (G := G)) := by
    apply LipschitzWith.of_dist_le_mul
    intro A B
    calc
      dist (pointwiseCLM A) (pointwiseCLM B) = ‖pointwiseCLM A-pointwiseCLM B‖ := dist_eq_norm _ _
      _ ≤ ‖A-B‖ := norm_sub_pointwiseCLM_le A B
      _ = (1 : NNReal) * dist A B := by
        simp only [NNReal.coe_one, one_mul]
        exact (dist_eq_norm A B).symm
  exact hL.continuous.comp (uniformContinuous_superposition hD).continuous
section SourceExtension

variable [FiniteDimensional ℝ E]

/-- A source Cⁿ near a compact state range has a global compactly supported Cⁿ extension agreeing on
that range. No regularity of a solution is assumed. -/
lemma exists_compactly_supported_extension {n : ℕ∞} {K U : Set E} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) {f : E → G}
    (hf : ∀ x ∈ U, ContDiffAt ℝ n f x) :
    ∃ g : E → G, ContDiff ℝ n g ∧ HasCompactSupport g ∧ EqOn g f K := by
  obtain ⟨R, hKR⟩ := hK.isBounded.subset_ball (0 : E)
  obtain ⟨V, hV, hKV, hVU⟩ := hK.exists_isOpen_closure_subset
    ((hU.inter isOpen_ball).mem_nhdsSet.mpr (subset_inter hKU hKR))
  obtain ⟨χ, hχ, _hχrange, hχsupp, hχone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := n) hV hK.isClosed hKV
  refine ⟨fun x => χ x • f x, ?_, ?_, ?_⟩
  · apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ tsupport χ
    · have hxU : x ∈ U := (hVU (by simpa [tsupport, hχsupp] using hx)).1
      exact hχ.contDiffAt.smul (hf x hxU)
    · apply (contDiffAt_const (c := (0 : G))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      simp [hy]
  · apply IsCompact.of_isClosed_subset (isCompact_closedBall (0 : E) R)
      (isClosed_tsupport _)
    have hsupp : tsupport χ ⊆ U ∩ ball (0 : E) R := by
      simpa only [tsupport, hχsupp] using hVU
    exact (tsupport_smul_subset_left χ f).trans
      (hsupp.trans (inter_subset_right.trans ball_subset_closedBall))
  · intro x hx
    change χ x • f x = f x
    rw [(hχone x).mp hx, one_smul]

end SourceExtension
/-- Pair two compact continuous maps by a bounded real linear operator. -/
@[expose] noncomputable def continuousMapPair : C(K,E) × C(K,G) →L[ℝ] C(K,E×G) :=
  LinearMap.mkContinuous
    { toFun := fun z => z.1.prodMk z.2
      map_add' := by intros; ext <;> rfl
      map_smul' := by intros; ext <;> rfl }
    1 (by
      intro z
      change ‖z.1.prodMk z.2‖ ≤ 1 * ‖z‖
      rw [one_mul]
      apply (ContinuousMap.norm_le _ (norm_nonneg z)).mpr
      intro t
      exact max_le ((z.1.norm_coe_le_norm t).trans (le_max_left ‖z.1‖ ‖z.2‖))
        ((z.2.norm_coe_le_norm t).trans (le_max_right ‖z.1‖ ‖z.2‖)))

/-- Multiply compact continuous vector-valued maps by a fixed continuous real weight. -/
@[expose] noncomputable def continuousMapSMul (w : C(K, ℝ)) : C(K,E) →L[ℝ] C(K,E) :=
  LinearMap.mkContinuous
    { toFun := fun z => w • z
      map_add' := by intros; ext; simp [smul_add]
      map_smul' := by intros; ext; simp [smul_smul, mul_comm] }
    ‖w‖ (by
      intro z
      change ‖w • z‖ ≤ ‖w‖ * ‖z‖
      apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg w) (norm_nonneg z))).mpr
      intro t
      exact (norm_smul (w t) (z t)).trans_le
        (mul_le_mul (w.norm_coe_le_norm t) (z.norm_coe_le_norm t)
          (norm_nonneg _) (norm_nonneg _)))


/-- Compactly supported C¹ maps have uniformly continuous first state
derivatives, so their superposition maps are C¹ without a second
derivative hypothesis. -/
theorem contDiff_superposition_compactSupport {f : E → G}
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) :
    ContDiff ℝ 1 (superposition f hf.continuous (K := K)) := by
  exact contDiff_superposition_of_uniformContinuous
    (fun x => (hf.differentiable_one x).hasFDerivAt)
    ((hfc.fderiv ℝ).uniformContinuous_of_continuous
      (hf.continuous_fderiv (by decide)))

/-- A compactly supported C¹ map is globally Lipschitz. Its finite
coefficient depends only on the map, before any solution is chosen. -/
theorem compactSupport_lipschitz {f : E → G}
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) :
    ∃ L : NNReal, LipschitzWith L f := by
  obtain ⟨C, hC⟩ := (hfc.fderiv ℝ).exists_bound_of_continuous
    (hf.continuous_fderiv (by decide))
  let L : NNReal := ⟨max 0 C, le_max_left _ _⟩
  refine ⟨L, lipschitzWith_of_nnnorm_fderiv_le hf.differentiable_one ?_⟩
  intro x
  exact_mod_cast (hC x).trans (le_max_right 0 C)

/-- The reciprocal of a nowhere-zero continuous scalar weight. -/
@[expose] noncomputable def inverseWeight (w : C(K, ℝ)) (hw : ∀ t, w t ≠ 0) : C(K,ℝ) :=
  ⟨fun t => (w t)⁻¹, w.continuous.inv₀ hw⟩

/-- Superposition conjugated by a fixed positive weight. This is the
nonlinear source map in exponentially weighted rectangle coordinates. -/
@[expose] noncomputable def weightedSuperposition (w : C(K, ℝ)) (hw : ∀ t, w t ≠ 0)
    (f : E → G) (hf : Continuous f) : C(K,E) → C(K,G) :=
  fun z => continuousMapSMul (inverseWeight w hw)
    (superposition f hf (continuousMapSMul w z))

/-- Weight conjugation preserves C¹ superposition for compactly supported
C¹ state maps. It introduces no derivative of a candidate solution. -/
theorem contDiff_weightedSuperposition (w : C(K, ℝ)) (hw : ∀ t, w t ≠ 0)
    {f : E → G} (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) :
    ContDiff ℝ 1 (weightedSuperposition w hw f hf.continuous) := by
  exact (continuousMapSMul (inverseWeight w hw)).contDiff.comp
    ((contDiff_superposition_compactSupport hf hfc).comp (continuousMapSMul w).contDiff)

/-- Pointwise weight factors cancel exactly in the source difference
estimate. The global source coefficient `L` is unchanged by conjugation,
uniformly in the weight and all continuous candidate states. -/
theorem lipschitzWith_weightedSuperposition (w : C(K, ℝ)) (hw : ∀ t, w t ≠ 0)
    {f : E → G} {L : NNReal} (hf : LipschitzWith L f) :
    LipschitzWith L (weightedSuperposition w hw f hf.continuous) := by
  apply LipschitzWith.of_dist_le_mul
  intro z z'
  rw [dist_eq_norm, dist_eq_norm]
  apply (ContinuousMap.norm_le _ (mul_nonneg L.2 (norm_nonneg (z-z')))).mpr
  intro t
  change ‖(w t)⁻¹ • f (w t • z t) - (w t)⁻¹ • f (w t • z' t)‖ ≤ L * ‖z-z'‖
  rw [← smul_sub, norm_smul]
  calc
    ‖(w t)⁻¹‖ * ‖f (w t • z t) - f (w t • z' t)‖
        ≤ ‖(w t)⁻¹‖ * (L * ‖w t • z t - w t • z' t‖) :=
      mul_le_mul_of_nonneg_left (hf.norm_sub_le _ _) (norm_nonneg _)
    _ = L * ‖z t-z' t‖ := by
      rw [← smul_sub, norm_smul, norm_inv]
      have hnorm : ‖w t‖ ≠ 0 := norm_ne_zero_iff.mpr (hw t)
      calc
        ‖w t‖⁻¹ * (L * (‖w t‖ * ‖z t-z' t‖)) =
            (‖w t‖⁻¹ * ‖w t‖) * (L * ‖z t-z' t‖) := by ring
        _ = L * ‖z t-z' t‖ := by rw [inv_mul_cancel₀ hnorm, one_mul]
    _ ≤ L * ‖z-z'‖ := mul_le_mul_of_nonneg_left ((z-z').norm_coe_le_norm t) L.2

end EmcsfAcExtension.Local.StripFunctionSpace
