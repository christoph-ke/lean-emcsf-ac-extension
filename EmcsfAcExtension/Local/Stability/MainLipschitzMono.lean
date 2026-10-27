module

public import EmcsfAcExtension.Local.Stability.MainRecords
public import EmcsfAcExtension.Local.Stability.SourceDifferenceCoefficient
public import EmcsfAcExtension.Local.Stability.SourceDifferenceCharge
public import EmcsfAcExtension.Local.Stability.SourceDifferencePhase
public import EmcsfAcExtension.Local.Stability.KCloseFlux

/-! # Increasing the common comparison constant

Each input record is monotone in its estimate constant on the nonnegative
small-data scope. This permits a finite maximum before choosing the pair.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local.Stab

/-- [internal] Increasing the radial comparison constant, with all physical
scales retained. There is no implicit constant. -/
theorem RatioDifferences.mono {C D e T ε M δ : ℝ} {S₁ S₂ : Fields}
    (hr : RatioDifferences C e T ε M δ S₁ S₂)
    (hCD : C ≤ D) (hε : 0 ≤ ε) (hM : 0 ≤ M) (hδ : 0 ≤ δ) :
    RatioDifferences D e T ε M δ S₁ S₂ := by
  have hσ : 0 ≤ sigma e M T := by unfold sigma; positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp
    exact (hr.out_pointwise p hp).trans (mul_le_mul_of_nonneg_right hCD (by positivity))
  · intro p hp
    exact (hr.in_pointwise p hp).trans (mul_le_mul_of_nonneg_right hCD (by positivity))
  · intro u hu
    exact (hr.out_hardy u hu).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hCD (by positivity)))
  · intro v hv
    exact (hr.in_hardy v hv).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hCD (by positivity)))

/-- [internal] Increasing the field comparison constant. All factors are
explicit and independent of derivative suprema. -/
theorem FieldDifference.mono {C D T ε δ : ℝ} {S₁ S₂ : Fields}
    (hr : FieldDifference C T ε δ S₁ S₂)
    (hCD : C ≤ D) (hε : 0 ≤ ε) (hδ : 0 ≤ δ) :
    FieldDifference D T ε δ S₁ S₂ := by
  constructor
  intro p hp
  exact (hr.bound p hp).trans (mul_le_mul_of_nonneg_right hCD (by positivity))

/-- [internal] Increasing the radius-weighted charge comparison constant.
The coupling and background factors remain explicit. -/
theorem ChargeDifference.mono {C D e T ε M δ : ℝ} {S₁ S₂ : Fields}
    (hr : ChargeDifference C e T ε M δ S₁ S₂)
    (hCD : C ≤ D) (hε : 0 ≤ ε) (hM : 0 ≤ M) (hδ : 0 ≤ δ) :
    ChargeDifference D e T ε M δ S₁ S₂ := by
  constructor
  intro p hp hlt
  apply (hr.bound p hp hlt).trans
  gcongr

/-- [internal] Increasing the potential comparison constant while retaining
its full length factor. All numerical multipliers are exactly one. -/
theorem PotentialDifference.mono {C D e T ε M δ : ℝ} {S₁ S₂ : Fields}
    (hr : PotentialDifference C e T ε M δ S₁ S₂)
    (hCD : C ≤ D) (hT : 0 ≤ T) (hε : 0 ≤ ε) (hM : 0 ≤ M) (hδ : 0 ≤ δ) :
    PotentialDifference D e T ε M δ S₁ S₂ := by
  constructor
  apply hr.bound.trans
  apply ENNReal.ofReal_le_ofReal
  gcongr

/-- [internal] Increasing the incoming flux comparison constant. Its
`σε²H/M` scale is retained exactly. -/
theorem IncomingFluxDifference.mono {C D e T ε M δ : ℝ} {S₁ S₂ : Fields}
    (hr : IncomingFluxDifference C e T ε M δ S₁ S₂)
    (hCD : C ≤ D) (hε : 0 ≤ ε) (hM : 0 ≤ M) (hδ : 0 ≤ δ) :
    IncomingFluxDifference D e T ε M δ S₁ S₂ := by
  have hσ : 0 ≤ sigma e M T := by unfold sigma; positivity
  constructor
  intro v hv
  exact (hr.bound v hv).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right hCD (by positivity)))

/-- [internal] Increasing the outgoing flux comparison constant. There is
no change to the literal signed k coefficient. -/
theorem OutgoingFluxDifference.mono {C D T ε : ℝ} {S₁ S₂ : Fields}
    (hr : OutgoingFluxDifference C T ε S₁ S₂)
    (hCD : C ≤ D) (hε : 0 ≤ ε) :
    OutgoingFluxDifference D T ε S₁ S₂ := by
  constructor
  intro u hu
  exact (hr.bound u hu).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right hCD (by positivity)))

/-- [internal] Increasing the unabsorbed geometry comparison constant.
Every displayed coefficient remains uniform in the pair and all scales. -/
theorem GeometryDifference.mono {C D e T ε M δ : ℝ} {S₁ S₂ : Fields}
    (hr : GeometryDifference C e T ε M δ S₁ S₂)
    (hCD : C ≤ D) (hε : 0 ≤ ε) (hδ : 0 ≤ δ) :
    GeometryDifference D e T ε M δ S₁ S₂ := by
  have hσ : 0 ≤ sigma e M T := by unfold sigma; positivity
  constructor
  apply hr.bound.trans
  gcongr

end EmcsfAcExtension.Local.Stab
