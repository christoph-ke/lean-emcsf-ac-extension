module

public import Mathlib
public import EmcsfAcExtension.Frozen.Fields.Mu

/-! # Root A Observation

Literal objects from internal project record, adopted by internal project record.
Source: `source/charged_SF_new_version.tex`; individual declarations give line references.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal

namespace EmcsfAcExtension.Global

/-- [def-node sec:charged-observation#cylinder-energy]
Charged cylinder energy, charged_SF_new_version.tex:L1880–L1884. -/
noncomputable def cylinderEnergy (S : Fields) (b u v : ℝ) : ℝ :=
  b / 2 * (‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2 - Real.log (1 - S.mu u v))

/-- Unfold `cylinderEnergy` to the source formula above. -/
theorem cylinderEnergy_def (S : Fields) (b u v : ℝ) :
    cylinderEnergy S b u v =
  b / 2 * (‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2 - Real.log (1 - S.mu u v)) := rfl

/-- [internal]
Measured square difference in the boundary clock, charged_SF_new_version.tex:L2825–L2847. -/
noncomputable def cylinderDissipation (S : Fields) (U V : ℝ → ℝ) (s t : ℝ) : ℝ :=
  ∫ x in s..t, ‖S.theta (U x) (V x) / (S.lam (U x) (V x) : ℂ) -
    S.xi (U x) (V x) / (S.nu (U x) (V x) : ℂ)‖ ^ 2

/-- [internal]
Static inverse-radius ODE right side, charged_SF_new_version.tex:L2199–L2225. -/
noncomputable def staticInvRadiusRHS (P : ℂ) (q x : ℝ) (z : ℝ × ℝ × ℂ) :
    ℝ × ℝ × ℂ :=
  (-(1 - 2 * x * z.1) * ‖P‖ ^ 2 / (8 * z.2.1 ^ 2) - q ^ 2 / 2,
   -z.2.1 * (2 * z.1 - q ^ 2 * x) / (1 - 2 * x * z.1),
   P / (2 * z.2.1 : ℝ))

/-- [def-node prop:charged-observation#comparison-variables]
Shifted radius-weighted scalar, charged_SF_new_version.tex:L2332–L2344. -/
noncomputable def shiftedRphi (S : Fields) (H : ℂ) (u v : ℝ) : ℂ :=
  S.r u v * (S.phi u v - H)

/-- [def-node prop:charged-observation#comparison-variables]
Scalar comparison difference, charged_SF_new_version.tex:L2332–L2355. -/
noncomputable def scalarComparison (S : Fields) (H : ℂ) (phiStar : ℝ → ℂ)
    (u v : ℝ) : ℂ :=
  shiftedRphi S H u v - S.r u v * phiStar (S.r u v)

/-- [def-node prop:charged-observation#comparison-variables]
Mass comparison difference, charged_SF_new_version.tex:L2332–L2355. -/
noncomputable def massComparison (S : Fields) (mStar : ℝ → ℝ) (u v : ℝ) : ℝ :=
  S.m u v - mStar (S.r u v)

/-- [def-node prop:charged-observation#comparison-variables]
Region supremum comparison norm, charged_SF_new_version.tex:L2652–L2657. -/
noncomputable def comparisonNorm {E : Type*} [NormedAddCommGroup E]
    (D : Set (ℝ × ℝ)) (f : ℝ → ℝ → E) : ℝ≥0∞ :=
  ⨆ p ∈ D, ‖f p.1 p.2‖ₑ

end EmcsfAcExtension.Global
