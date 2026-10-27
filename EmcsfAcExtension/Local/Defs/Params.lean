module

public import EmcsfAcExtension.Frozen.Triangle
public import EmcsfAcExtension.Frozen.DatumVar
public import EmcsfAcExtension.Frozen.Fields.NormalizedOut

/-! # Local data and parameters

Literal internal definitions from internal project record and
`source/charged_SF_new_version.tex`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- [internal]
`M = 1 + |φ(0,0)| + 10ε` with `φ(0,0) = h(0)`, `ε = TV_{[0,T]} h`
(charged_SF_new_version.tex:L4407–4410). -/
noncomputable def datumM (h : ℝ → ℂ) (T : ℝ) : ℝ := 1 + ‖h 0‖ + 10 * datumVar h T

/-- Unfold `datumM` to its literal internal project record formula. -/
theorem datumM_def (h : ℝ → ℂ) (T : ℝ) :
    datumM h T =
  1 + ‖h 0‖ + 10 * datumVar h T := rfl

/-- [internal]
The dimensionless charged length scale `|e| R M`, `R = T/2` (charged_SF_new_version.tex:L4411–4412).
-/
noncomputable def chargedScale (e : ℝ) (h : ℝ → ℂ) (T : ℝ) : ℝ := |e| * (T / 2) * datumM h T

/-- Unfold `chargedScale` to its literal internal project record formula. -/
theorem chargedScale_def (e : ℝ) (h : ℝ → ℂ) (T : ℝ) :
    chargedScale e h T =
  |e| * (T / 2) * datumM h T := rfl

/-- [internal]
`σ = e² M² R²`, `R = T/2` (charged_SF_new_version.tex:L4969–4970). -/
noncomputable def sigma (e M T : ℝ) : ℝ := e ^ 2 * M ^ 2 * (T / 2) ^ 2

/-- [def-node restart-sec-bv-stability-independent#comparison-distances]
`Δ₀ = |δ(α/λ)(0,0)| + TV_{[0,T]} δ(α/λ)(0,·)` (charged_SF_new_version.tex:L5061–5089), in the frozen
form. -/
noncomputable def dataDist (h₁ h₂ : ℝ → ℂ) (T : ℝ) : ℝ := ‖h₁ 0 - h₂ 0‖ + datumVar (h₁ - h₂) T

/-- [internal]
The boundary conditions of the fixed null problem (charged_SF_new_version.tex:L4403–4407,
  charged_SF_new_version.tex:L5932–5936), literally the
frozen anchor's premises: `r(0,v) = v/2`, `(α/λ)(0,v) = h(v)`, `A_u(t,t) = 0`. -/
def IsRestartData (S : Fields) (h : ℝ → ℂ) (T : ℝ) : Prop :=
  (∀ v ∈ Icc 0 T, S.r 0 v = v / 2 ∧ S.a 0 v = h v) ∧ ∀ t ∈ Icc 0 T, S.A t t = 0

/-- [def-node restart-sec-independent-null-construction#fixed-null-problem]
Complete AC-datum fixed null problem (charged_SF_new_version.tex:L5932–5943).
The carrier, initial radius, normalized datum and axis potential are explicit;
`Fields` already fixes `A_v = 0`. The positive thresholds bound precisely `ε`
and `|e| M T`; no smallness is imposed on the constant scalar value. `M` is
the arbitrary datum sup bound of this definition, not an assertion of the
broader construction theorem excluded by internal project record's binding note S2.
This internal predicate, authorized by internal project record, must never enter a
frozen statement. AC guards every use of the real-valued `datumVar`. -/
def Null.FixedNullProblem (e T ε M ε₀ δ₀ : ℝ) (D : Set (ℝ × ℝ))
    (S : Fields) (h : ℝ → ℂ) : Prop :=
  0 < T ∧ D = triangle 0 T ∧ IsRestartData S h T ∧
    AbsolutelyContinuousOnInterval h 0 T ∧ datumVar h T ≤ ε ∧
    (∀ v ∈ Icc 0 T, ‖h v‖ ≤ M) ∧
    0 < ε₀ ∧ 0 < δ₀ ∧ 0 ≤ ε ∧ ε ≤ ε₀ ∧ |e| * M * T ≤ δ₀

end EmcsfAcExtension.Local
