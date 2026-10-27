module

public import EmcsfAcExtension.Global.Defs.Curves
public import EmcsfAcExtension.Frozen.IsSolution
public import EmcsfAcExtension.Infra.Level.Clock

/-! # Constant-radius cylinders in the boundary clock

The clock of `charged_SF_new_version.tex:L1862` is the integral clock of the level-set
infrastructure. Its inverse gives both coordinate rates, including endpoints.
No quantitative bound uniform in the cylinder is asserted here.
-/

public section

open Set MeasureTheory Filter Topology
open scoped NNReal

namespace EmcsfAcExtension.Global

namespace Cylinder

/-- [node sec:charged-observation#cylinder-clock]
The source clock is exactly the positive-density integral clock. -/
theorem cylinder_clock (S : Fields) (v : ℝ → ℝ) (a u : ℝ) :
    cylinderClock S v a u = Level.integralClock (fun x => -S.nu x (v x)) a u := rfl

/-- [internal] A proper C¹ radius graph has a clock cylinder with the actual
source clock as duration and with the original two endpoints. Compact clock
bounds may depend on this graph; no universal constant is selected. -/
theorem exists_clockCylinder_of_levelGraph {e : ℝ} {S : Fields}
    {D : Set (ℝ × ℝ)} (hS : IsSolution e S D) {v : ℝ → ℝ} {a c b : ℝ}
    (hac : a < c) (hv : ContDiffOn ℝ 1 v (Icc a c))
    (hmem : ∀ u ∈ Icc a c, (u, v u) ∈ D)
    (hr : ∀ u ∈ Icc a c, S.r u (v u) = b)
    (hspeed : ∀ u ∈ Icc a c,
      HasDerivWithinAt v (-S.nu u (v u) / S.lam u (v u)) (Icc a c) u) :
    ∃ T > 0, T = cylinderClock S v a c ∧
      ∃ γ : ClockCylinder S D b 0 T,
        γ.U 0 = a ∧ γ.U T = c ∧ γ.V 0 = v a ∧ γ.V T = v c ∧
          ∀ τ ∈ Icc 0 T, γ.U τ ∈ Icc a c ∧ γ.V τ = v (γ.U τ) := by
  have hc : ContinuousOn (fun u => -S.nu u (v u)) (Icc a c) :=
    (hS.cont_nu.comp (continuousOn_id.prodMk hv.continuousOn) hmem).neg
  obtain ⟨T, hT, hclock, U, V, hU, hV, hU₀, hUT, hV₀, hVT, h⟩ :=
    Level.exists_clockParametrization_of_levelGraph hac hv hr hc
      (fun u hu => hS.nu_neg _ (hmem u hu)) hspeed
  let γ : ClockCylinder S D b 0 T :=
    { U := U, V := V, c1_U := hU, c1_V := hV
      mem := fun τ hτ => by rw [(h τ hτ).2.1]; exact hmem _ (h τ hτ).1
      radius := fun τ hτ => (h τ hτ).2.2.1
      rate_U := fun τ hτ => (h τ hτ).2.2.2.1
      rate_V := fun τ hτ => (h τ hτ).2.2.2.2 }
  exact ⟨T, hT, hclock, γ, hU₀, hUT, hV₀, hVT,
    fun τ hτ => ⟨(h τ hτ).1, (h τ hτ).2.1⟩⟩

end Cylinder

private theorem exists_antilipschitz_of_positive_rate
    {f w : ℝ → ℝ} {s t : ℝ}
    (hf : ContinuousOn f (Icc s t)) (hw : ContinuousOn w (Icc s t))
    (hp : ∀ x ∈ Icc s t, 0 < w x)
    (hd : ∀ x ∈ Icc s t, HasDerivWithinAt f (w x) (Icc s t) x) :
    ∃ L : ℝ≥0, AntilipschitzWith L ((Icc s t).domRestrict f) := by
  obtain ⟨m, hm, hml⟩ := isCompact_Icc.exists_forall_le' hw hp
  have hdiff : DifferentiableOn ℝ f (interior (Icc s t)) := by
    intro x hx
    rw [interior_Icc] at hx
    exact ((hd x (Ioo_subset_Icc_self hx)).hasDerivAt
      (Icc_mem_nhds hx.1 hx.2)).differentiableAt.differentiableWithinAt
  have hlower : ∀ x ∈ Icc s t, ∀ y ∈ Icc s t, x ≤ y →
      m * (y - x) ≤ f y - f x :=
    (convex_Icc s t).mul_sub_le_image_sub_of_le_deriv hf hdiff (by
      intro x hx
      rw [interior_Icc] at hx
      rw [((hd x (Ioo_subset_Icc_self hx)).hasDerivAt
        (Icc_mem_nhds hx.1 hx.2)).deriv]
      exact hml x (Ioo_subset_Icc_self hx))
  have hmono : MonotoneOn f (Icc s t) := by
    intro x hx y hy hxy
    have hh := hlower x hx y hy hxy
    have hp' := mul_nonneg hm.le (sub_nonneg.mpr hxy)
    linarith
  refine ⟨⟨m⁻¹, inv_nonneg.mpr hm.le⟩, ?_⟩
  apply AntilipschitzWith.of_le_mul_dist
  intro x y
  change dist (x : ℝ) (y : ℝ) ≤ m⁻¹ * dist (f x) (f y)
  wlog hxy : (x : ℝ) ≤ y generalizing x y
  · simpa only [dist_comm] using this y x (le_of_not_ge hxy)
  rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxy),
    Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (hmono x.property y.property hxy))]
  have hh := hlower x x.property y y.property hxy
  calc
    -((x : ℝ) - y) = ((y : ℝ) - x) := by ring
    _ ≤ m⁻¹ * (f y - f x) := (le_inv_mul_iff₀ hm).mpr hh
    _ = m⁻¹ * -(f x - f y) := by ring

namespace ClockCylinder

/-- [internal] Continuous fields have their specified continuous cylinder traces. -/
theorem continuousOn_trace {E : Type*} [TopologicalSpace E] {S : Fields}
    {D : Set (ℝ × ℝ)} {b s t : ℝ} (γ : ClockCylinder S D b s t)
    {f : ℝ → ℝ → E} (hf : ContinuousOn (Function.uncurry f) D) :
    ContinuousOn (fun τ => f (γ.U τ) (γ.V τ)) (Icc s t) :=
  hf.comp (γ.c1_U.continuousOn.prodMk γ.c1_V.continuousOn) γ.mem

/-- [internal] The incoming clock rate is an ordinary derivative in the open
clock interval; endpoint derivatives remain within derivatives in the record. -/
theorem hasDerivAt_U {S : Fields} {D : Set (ℝ × ℝ)} {b s t τ : ℝ}
    (γ : ClockCylinder S D b s t) (hτ : τ ∈ Ioo s t) :
    HasDerivAt γ.U (-S.nu (γ.U τ) (γ.V τ))⁻¹ τ :=
  (γ.rate_U τ (Ioo_subset_Icc_self hτ)).hasDerivAt (Icc_mem_nhds hτ.1 hτ.2)

/-- [internal] The outgoing clock rate is an ordinary derivative in the open
clock interval. -/
theorem hasDerivAt_V {S : Fields} {D : Set (ℝ × ℝ)} {b s t τ : ℝ}
    (γ : ClockCylinder S D b s t) (hτ : τ ∈ Ioo s t) :
    HasDerivAt γ.V (S.lam (γ.U τ) (γ.V τ))⁻¹ τ :=
  (γ.rate_V τ (Ioo_subset_Icc_self hτ)).hasDerivAt (Icc_mem_nhds hτ.1 hτ.2)

/-- [internal] The incoming coordinate increases strictly along a clock cylinder. -/
theorem strictMonoOn_U {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)} {b s t : ℝ}
    (γ : ClockCylinder S D b s t) (hS : IsSolution e S D) :
    StrictMonoOn γ.U (Icc s t) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc s t) γ.c1_U.continuousOn
  intro τ hτ
  rw [interior_Icc] at hτ
  rw [(γ.hasDerivAt_U hτ).deriv]
  exact inv_pos.mpr (neg_pos.mpr (hS.nu_neg _ (γ.mem τ (Ioo_subset_Icc_self hτ))))

/-- [internal] The outgoing coordinate increases strictly along a clock cylinder. -/
theorem strictMonoOn_V {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)} {b s t : ℝ}
    (γ : ClockCylinder S D b s t) (hS : IsSolution e S D) :
    StrictMonoOn γ.V (Icc s t) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc s t) γ.c1_V.continuousOn
  intro τ hτ
  rw [interior_Icc] at hτ
  rw [(γ.hasDerivAt_V hτ).deriv]
  exact inv_pos.mpr (hS.lam_pos _ (γ.mem τ (Ioo_subset_Icc_self hτ)))

/-- [internal] Both clock labels are bi-Lipschitz on the closed cylinder.
The four constants may depend on the solution and this proper segment;
no bound uniform at the missing endpoint is asserted. -/
theorem exists_biLipschitz_labels {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)} {b s t : ℝ}
    (γ : ClockCylinder S D b s t) (hS : IsSolution e S D) :
    ∃ KU KV LU LV : ℝ≥0,
      LipschitzOnWith KU γ.U (Icc s t) ∧ LipschitzOnWith KV γ.V (Icc s t) ∧
      AntilipschitzWith LU ((Icc s t).domRestrict γ.U) ∧
      AntilipschitzWith LV ((Icc s t).domRestrict γ.V) := by
  obtain ⟨KU, hKU⟩ := γ.c1_U.exists_lipschitzOnWith one_ne_zero (convex_Icc s t) isCompact_Icc
  obtain ⟨KV, hKV⟩ := γ.c1_V.exists_lipschitzOnWith one_ne_zero (convex_Icc s t) isCompact_Icc
  have hnu := (γ.continuousOn_trace hS.cont_nu).neg
  have hlam := γ.continuousOn_trace hS.cont_lam
  obtain ⟨LU, hLU⟩ := exists_antilipschitz_of_positive_rate γ.c1_U.continuousOn
    (hnu.inv₀ (fun x hx => (neg_pos.mpr (hS.nu_neg _ (γ.mem x hx))).ne'))
    (fun x hx => inv_pos.mpr (neg_pos.mpr (hS.nu_neg _ (γ.mem x hx)))) γ.rate_U
  obtain ⟨LV, hLV⟩ := exists_antilipschitz_of_positive_rate γ.c1_V.continuousOn
    (hlam.inv₀ (fun x hx => (hS.lam_pos _ (γ.mem x hx)).ne'))
    (fun x hx => inv_pos.mpr (hS.lam_pos _ (γ.mem x hx))) γ.rate_V
  exact ⟨KU, KV, LU, LV, hKU, hKV, hLU, hLV⟩

end ClockCylinder

end EmcsfAcExtension.Global
