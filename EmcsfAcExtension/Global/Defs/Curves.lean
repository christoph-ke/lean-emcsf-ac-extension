module

public import Mathlib
public import EmcsfAcExtension.Frozen.Fields
public import EmcsfAcExtension.Frozen.CovVarIn

/-! # Root A Curves

Literal objects from internal project record, adopted by internal project record.
Source: `source/charged_SF_new_version.tex`; individual declarations give line references.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal

namespace EmcsfAcExtension.Global

/-- [def-node sec:charged-observation#cylinder-clock]
Constant-radius clock integral, charged_SF_new_version.tex:L1862–L1867. -/
noncomputable def cylinderClock (S : Fields) (vb : ℝ → ℝ) (s u : ℝ) : ℝ :=
  ∫ t in s..u, -S.nu t (vb t)

/-- Unfold `cylinderClock` to the source formula above. -/
theorem cylinderClock_def (S : Fields) (vb : ℝ → ℝ) (s u : ℝ) :
    cylinderClock S vb s u =
  ∫ t in s..u, -S.nu t (vb t) := rfl

/-- [def-node sec:charged-equations#covariant-variation]
Unitary parallel representative along a curve, charged_SF_new_version.tex:L882–L882. -/
noncomputable def curveParallel (e : ℝ) (S : Fields) (f : ℝ → ℝ → ℂ)
    (U V : ℝ → ℝ) (s x : ℝ) : ℂ :=
  Complex.exp (I * e * ∫ y in s..x, S.A (U y) (V y) * deriv U y) * f (U x) (V x)

/-- Unfold `curveParallel` to the source formula above. -/
theorem curveParallel_def (e : ℝ) (S : Fields) (f : ℝ → ℝ → ℂ)
    (U V : ℝ → ℝ) (s x : ℝ) :
    curveParallel e S f U V s x =
  Complex.exp (I * e * ∫ y in s..x, S.A (U y) (V y) * deriv U y) * f (U x) (V x) := rfl

/-- [def-node sec:charged-observation#cylinder-covariant-variation]
Covariant curve variation, charged_SF_new_version.tex:L1898–L1901. -/
noncomputable def curveCovVar (e : ℝ) (S : Fields) (f : ℝ → ℝ → ℂ)
    (U V : ℝ → ℝ) (s t : ℝ) : ℝ≥0∞ :=
  eVariationOn (curveParallel e S f U V s) (Icc s t)

/-- Unfold `curveCovVar` to the source formula above. -/
theorem curveCovVar_def (e : ℝ) (S : Fields) (f : ℝ → ℝ → ℂ)
    (U V : ℝ → ℝ) (s t : ℝ) :
    curveCovVar e S f U V s t =
  eVariationOn (curveParallel e S f U V s) (Icc s t) := rfl

/-- [internal]
Parametrized radius level curve with clock derivatives, charged_SF_new_version.tex:L1862–L1866. -/
structure ClockCylinder (S : Fields) (D : Set (ℝ × ℝ)) (b s t : ℝ) where
  /-- Incoming coordinate map. -/
  U : ℝ → ℝ
  /-- Outgoing coordinate map. -/
  V : ℝ → ℝ
  /-- C¹ incoming coordinate on the clock interval. -/
  c1_U : ContDiffOn ℝ 1 U (Icc s t)
  /-- C¹ outgoing coordinate on the clock interval. -/
  c1_V : ContDiffOn ℝ 1 V (Icc s t)
  /-- The curve remains in the specified domain. -/
  mem : ∀ x ∈ Icc s t, (U x, V x) ∈ D
  /-- The curve has the specified constant radius. -/
  radius : ∀ x ∈ Icc s t, S.r (U x) (V x) = b
  /-- Incoming derivative in the boundary clock. -/
  rate_U : ∀ x ∈ Icc s t,
    HasDerivWithinAt U ((-S.nu (U x) (V x))⁻¹) (Icc s t) x
  /-- Outgoing derivative in the boundary clock. -/
  rate_V : ∀ x ∈ Icc s t,
    HasDerivWithinAt V ((S.lam (U x) (V x))⁻¹) (Icc s t) x

end EmcsfAcExtension.Global
