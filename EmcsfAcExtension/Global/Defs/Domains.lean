module

public import Mathlib
public import EmcsfAcExtension.Frozen.OrigDomain
public import EmcsfAcExtension.Frozen.Fields

/-! # Root A Domains

Literal objects from internal project record, adopted by internal project record.
Source: `source/charged_SF_new_version.tex`; individual declarations give line references.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal

namespace EmcsfAcExtension.Global

/-- [internal]
Finite-cutoff exterior, charged_SF_new_version.tex:L3935–L3945. -/
def exteriorDomain (ui u₀ u₁ : ℝ) (vb : ℝ → ℝ) : Set (ℝ × ℝ) :=
  origDomain ui ∩ {p | u₀ ≤ p.1 ∧ p.1 ≤ u₁ ∧ vb p.1 ≤ p.2}

/-- [internal]
Adaptive original exterior, charged_SF_new_version.tex:L1071–L1079. -/
def adaptiveExterior (S : Fields) (ui u₀ : ℝ) (ell : ℝ → ℝ) : Set (ℝ × ℝ) :=
  origDomain ui ∩ {p | u₀ ≤ p.1 ∧ ell (S.r p.1 0) ≤ S.r p.1 p.2}

/-- [internal]
Inward comparison window, charged_SF_new_version.tex:L1918–L1926 and L2737–L2755. -/
def comparisonDomain (S : Fields) (D : Set (ℝ × ℝ)) (U V : ℝ → ℝ)
    (s t b : ℝ) : Set (ℝ × ℝ) :=
  D ∩ (Icc (U s) (U t) ×ˢ Icc (V s) (V t)) ∩ {p | S.r p.1 p.2 ≤ b}

/-- [internal]
Normalized inward coordinate order, charged_SF_new_version.tex:L1980–L1988. -/
def sidewaysTriangle (a b : ℝ) : Set (ℝ × ℝ) :=
  {p | a ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ b}

/-- [internal]
Positive-radius comparison truncation, charged_SF_new_version.tex:L2750–L2754. -/
def sidewaysTruncation (S : Fields) (D : Set (ℝ × ℝ)) (a b r₀ L : ℝ) :
    Set (ℝ × ℝ) :=
  D ∩ sidewaysTriangle a b ∩ {p | r₀ ≤ S.r p.1 p.2 ∧ S.r p.1 p.2 ≤ L}

end EmcsfAcExtension.Global
