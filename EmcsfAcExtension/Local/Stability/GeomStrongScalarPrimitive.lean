module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.MomentsSections
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity

/-! # The four geometric scalar primitive differences

The outer coefficient, inner radius, incoming scalar ratio and outgoing
renormalized derivative are subtracted separately at common labels.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Local

/-- The complex scalar primitive in the common geometric source, before
taking its real part. This auxiliary expression uses the exact outer
geometric coefficient and is totalized at the axis. -/
@[expose] noncomputable def geometricScalarSource (D : Set (ℝ × ℝ))
    (S : Fields) (u v : ℝ) : ℂ :=
  ((2 * S.nu u v * S.lam u v / ((1 - S.mu u v) * S.r u v ^ 2) : ℝ) : ℂ) *
    curvScalar D S u v

private theorem primitive_telescope_aux {u v : ℝ} (huv : u ≤ v)
    {r₁ r₂ : ℝ → ℝ} {y₁ y₂ j₁ j₂ : ℝ → ℂ} (c₁ c₂ : ℂ)
    (cr₁ : ContinuousOn r₁ (Icc u v)) (cr₂ : ContinuousOn r₂ (Icc u v))
    (cy₁ : ContinuousOn y₁ (Icc u v)) (cy₂ : ContinuousOn y₂ (Icc u v))
    (cj₁ : ContinuousOn j₁ (Icc u v)) (cj₂ : ContinuousOn j₂ (Icc u v)) :
    c₁ * (∫ w in u..v, (r₁ w : ℂ) * starRingEnd ℂ (y₁ w) * j₁ w) -
      c₂ * (∫ w in u..v, (r₂ w : ℂ) * starRingEnd ℂ (y₂ w) * j₂ w) =
    (c₁ - c₂) * (∫ w in u..v, (r₂ w : ℂ) * starRingEnd ℂ (y₂ w) * j₂ w) +
      c₁ * (∫ w in u..v, ((r₁ w - r₂ w : ℝ) : ℂ) * starRingEnd ℂ (y₂ w) * j₂ w) +
      c₁ * (∫ w in u..v, (r₁ w : ℂ) * starRingEnd ℂ (y₁ w - y₂ w) * j₂ w) +
      c₁ * (∫ w in u..v, (r₁ w : ℂ) * starRingEnd ℂ (y₁ w) * (j₁ w - j₂ w)) := by
  have cR₁ := Complex.continuous_ofReal.comp_continuousOn cr₁
  have cR₂ := Complex.continuous_ofReal.comp_continuousOn cr₂
  have i₁ := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) huv
    ((cR₁.mul cy₁.star).mul cj₁)
  have i₂ := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) huv
    ((cR₂.mul cy₂.star).mul cj₂)
  have ir := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) huv
    (((Complex.continuous_ofReal.comp_continuousOn (cr₁.sub cr₂)).mul cy₂.star).mul cj₂)
  have iy := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) huv
    ((cR₁.mul (cy₁.sub cy₂).star).mul cj₂)
  have ij := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) huv
    ((cR₁.mul cy₁.star).mul (cj₁.sub cj₂))
  have heq : (fun w => (r₁ w : ℂ) * starRingEnd ℂ (y₁ w) * j₁ w -
      (r₂ w : ℂ) * starRingEnd ℂ (y₂ w) * j₂ w) =
      (fun w => ((r₁ w - r₂ w : ℝ) : ℂ) * starRingEnd ℂ (y₂ w) * j₂ w +
        (r₁ w : ℂ) * starRingEnd ℂ (y₁ w - y₂ w) * j₂ w +
        (r₁ w : ℂ) * starRingEnd ℂ (y₁ w) * (j₁ w - j₂ w)) := by
    funext w
    simp only [Complex.ofReal_sub, map_sub]
    ring
  have hi := congrArg (fun f : ℝ → ℂ => ∫ w in u..v, f w) heq
  have hiSub := intervalIntegral.integral_sub i₁ i₂
  have hiAdd₁ := intervalIntegral.integral_add ir iy
  have hiAdd₂ := intervalIntegral.integral_add (ir.add iy) ij
  simp only [Pi.sub_apply, Pi.mul_apply, Function.comp_def] at hiSub hiAdd₁ hiAdd₂
  simp only [starRingEnd_apply] at hi ⊢
  rw [hiSub, hiAdd₂, hiAdd₁] at hi
  linear_combination c₁ * hi

private theorem scalar_coefficient_identity_aux (a g r : ℝ) (z : ℂ) :
    ((a / (g * r ^ 2) : ℝ) : ℂ) * ((r : ℂ)⁻¹ * z) =
      ((a / (g * r ^ 3) : ℝ) : ℂ) * z := by
  push_cast
  by_cases hr : r = 0
  · simp [hr]
  · have hrC := Complex.ofReal_ne_zero.mpr hr
    field_simp

/-- The scalar geometric source is the cubic outer coefficient times
its radial primitive. This algebraic identity has no regularity or
nonvanishing premise, since both sides are totalized at zero radius. -/
theorem geometricScalarSource_eq_cubic_primitive
    (D : Set (ℝ × ℝ)) (S : Fields) (u v : ℝ) :
    geometricScalarSource D S u v =
      ((2 * S.nu u v * S.lam u v / ((1 - S.mu u v) * S.r u v ^ 3) : ℝ) : ℂ) *
        ∫ w in u..v, (S.r u w : ℂ) *
          starRingEnd ℂ (S.xi u w / (S.nu u w : ℂ)) * jC1 D S u w := by
  exact scalar_coefficient_identity_aux
    (2 * S.nu u v * S.lam u v) (1 - S.mu u v) (S.r u v)
    (∫ w in u..v, (S.r u w : ℂ) *
      starRingEnd ℂ (S.xi u w / (S.nu u w : ℂ)) * jC1 D S u w)

private theorem primitive_section_continuity_aux
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h)
    {u v : ℝ} (hu : 0 ≤ u) (_huv : u ≤ v) (hvT : v ≤ T) :
    ContinuousOn (S.r u) (Icc u v) ∧
      ContinuousOn (fun w => S.xi u w / (S.nu u w : ℂ)) (Icc u v) ∧
      ContinuousOn (jC1 (triangle 0 T) S u) (Icc u v) := by
  have hm : MapsTo (fun w : ℝ => (u, w)) (Icc u v) (triangle 0 T) :=
    fun w hw => ⟨hu, hw.1, hw.2.trans hvT⟩
  refine ⟨?_, ?_, ?_⟩
  · exact hset.c1.c1_r.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn hm
  · exact (stab_in_ratio_c1 hset.c1).continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn hm
  · exact (continuousOn_jC1_aux hset.pos hset.c1).comp (f := fun w : ℝ => (u, w))
      (continuous_const.prodMk continuous_id).continuousOn hm

/-- Exact four-term subtraction for the geometric scalar source on the
classical triangle. There is no estimate constant or smallness premise;
each inner integral is justified by complete-section continuity.
-/
theorem stab_geometric_scalar_source_telescope_c1
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    let W₁ : ℂ := (2 * S₁.nu u v * S₁.lam u v /
      ((1 - S₁.mu u v) * S₁.r u v ^ 3) : ℝ)
    let W₂ : ℂ := (2 * S₂.nu u v * S₂.lam u v /
      ((1 - S₂.mu u v) * S₂.r u v ^ 3) : ℝ)
    geometricScalarSource (triangle 0 T) S₁ u v -
      geometricScalarSource (triangle 0 T) S₂ u v =
    (W₁ - W₂) * (∫ w in u..v, (S₂.r u w : ℂ) *
      starRingEnd ℂ (S₂.xi u w / (S₂.nu u w : ℂ)) * jC1 (triangle 0 T) S₂ u w) +
    W₁ * (∫ w in u..v, ((S₁.r u w - S₂.r u w : ℝ) : ℂ) *
      starRingEnd ℂ (S₂.xi u w / (S₂.nu u w : ℂ)) * jC1 (triangle 0 T) S₂ u w) +
    W₁ * (∫ w in u..v, (S₁.r u w : ℂ) *
      starRingEnd ℂ (S₁.xi u w / (S₁.nu u w : ℂ) - S₂.xi u w / (S₂.nu u w : ℂ)) *
        jC1 (triangle 0 T) S₂ u w) +
    W₁ * (∫ w in u..v, (S₁.r u w : ℂ) *
      starRingEnd ℂ (S₁.xi u w / (S₁.nu u w : ℂ)) *
        (jC1 (triangle 0 T) S₁ u w - jC1 (triangle 0 T) S₂ u w)) := by
  dsimp only
  let W (S : Fields) : ℂ := (2 * S.nu u v * S.lam u v /
    ((1 - S.mu u v) * S.r u v ^ 3) : ℝ)
  rw [geometricScalarSource_eq_cubic_primitive, geometricScalarSource_eq_cubic_primitive]
  obtain ⟨cr₁, cy₁, cj₁⟩ := primitive_section_continuity_aux h₁s hu huv.le hvT
  obtain ⟨cr₂, cy₂, cj₂⟩ := primitive_section_continuity_aux h₂s hu huv.le hvT
  have ht := primitive_telescope_aux huv.le (W S₁) (W S₂) cr₁ cr₂ cy₁ cy₂ cj₁ cj₂
  simpa only [W] using! ht

end EmcsfAcExtension.Local
