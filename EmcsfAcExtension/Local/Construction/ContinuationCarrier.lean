module

public import EmcsfAcExtension.Local.Defs.Picard
public import EmcsfAcExtension.Frozen.Triangle

/-! # Representation-independent outgoing-jet continuation carrier

The closed wedge and compatible continuous values/first jets are the
literal carrier interface used by the construction producers. Concrete
complete metric realizations may identify representatives outside the wedge.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Local

/-- The closed construction wedge `W(c,a,L)` of internal project record. -/
@[expose] def continuationWedge (c a L : ℝ) : Set (ℝ × ℝ) :=
  triangle c (c + L) ∩ {p | p.1 ≤ c + a}

/-- Continuous values and outgoing first jets satisfying sectional FTC.
The terminal collapsed section retains its specified limiting jet.
This is the representation-independent interface to internal project record's carrier. -/
structure ContinuationPair (c a L : ℝ) where
  /-- Outgoing expansion values. -/
  lam : ℝ → ℝ → ℝ
  /-- Normalized scalar values. -/
  hh : ℝ → ℝ → ℂ
  /-- Specified outgoing expansion jet. -/
  lamV : ℝ → ℝ → ℝ
  /-- Specified outgoing normalized scalar jet. -/
  hhV : ℝ → ℝ → ℂ
  /-- Joint continuity of the expansion values. -/
  continuous_lam : ContinuousOn (Function.uncurry lam) (continuationWedge c a L)
  /-- Joint continuity of the normalized scalar values. -/
  continuous_hh : ContinuousOn (Function.uncurry hh) (continuationWedge c a L)
  /-- Joint continuity of the expansion jet. -/
  continuous_lamV : ContinuousOn (Function.uncurry lamV) (continuationWedge c a L)
  /-- Joint continuity of the normalized scalar jet. -/
  continuous_hhV : ContinuousOn (Function.uncurry hhV) (continuationWedge c a L)
  /-- Expansion FTC, including the axis and the outer side. -/
  integral_lam : ∀ p ∈ continuationWedge c a L,
    lam p.1 p.2 = lam p.1 p.1 + ∫ s in p.1..p.2, lamV p.1 s
  /-- Normalized scalar FTC, including the axis and the outer side. -/
  integral_hh : ∀ p ∈ continuationWedge c a L,
    hh p.1 p.2 = hh p.1 p.1 + ∫ s in p.1..p.2, hhV p.1 s

/-- The two literal fixed-point equations, with initial factors on `u=c`.
There is no prescribed future-axis datum. -/
@[expose] def ContinuationPair.IsFixedPoint {c a L : ℝ} (Z : ContinuationPair c a L)
    (e : ℝ) (lam₀ : ℝ → ℝ) (h₀ : ℝ → ℂ) : Prop :=
  ∀ p ∈ continuationWedge c a L,
    Recon.picardLam e Z.lam Z.hh c lam₀ p.1 p.2 = Z.lam p.1 p.2 ∧
    Recon.picardH e Z.lam Z.hh c h₀ p.1 p.2 = Z.hh p.1 p.2

/-- The maximum-norm closed ball about the constant-in-`u` cone pair.
The radius bounds all four value/jet components, including boundary jets. -/
@[expose] def ContinuationPair.InConeBall {c a L : ℝ} (Z : ContinuationPair c a L)
    (lam₀ : ℝ → ℝ) (h₀ : ℝ → ℂ) (ρ : ℝ) : Prop :=
  ∀ p ∈ continuationWedge c a L,
    |Z.lam p.1 p.2 - lam₀ p.2| ≤ ρ ∧ ‖Z.hh p.1 p.2 - h₀ p.2‖ ≤ ρ ∧
    |Z.lamV p.1 p.2 - derivWithin lam₀ (Icc c (c + L)) p.2| ≤ ρ ∧
    ‖Z.hhV p.1 p.2 - derivWithin h₀ (Icc c (c + L)) p.2‖ ≤ ρ

end EmcsfAcExtension.Local
