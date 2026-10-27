module

public import EmcsfAcExtension.Local.Defs.C1Class
public import EmcsfAcExtension.Local.Defs.C1Bound
public import EmcsfAcExtension.Local.Defs.Picard
public import EmcsfAcExtension.Local.Defs.Params
public import EmcsfAcExtension.Local.Construction.OriginalPicardBall

/-! # Pending inputs for classical continuation

Literal first-jet interfaces for the construction route of internal project record and
internal project record. These internal propositions are proof obligations, not axioms.
Only `_of_inputs` helpers may consume them. Their producers are internal project record,
internal project record, respectively. No frozen theorem imports this module.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Local

/-- Pending internal project record input: the original-cone ball theorem of
internal project record (13)–(17). The canonical `datumM` is mandatory. The width
and a common Lipschitz coefficient are fixed before the datum in its
bounded first-jet class; the radius, lower expansion and gap are numerical. -/
@[expose] def ContinuationOriginalPicardInput : Prop :=
  ∀ T E M D : ℝ, 0 < T → 0 ≤ E → 1 ≤ M → 0 ≤ D →
    ∃ C a : ℝ, 0 < C ∧ 0 < a ∧ a ≤ T ∧ a*C < 1 ∧
    ∀ (e : ℝ) (h : ℝ → ℂ), |e| = E → datumM h T = M →
    ContDiffOn ℝ 1 h (Icc 0 T) →
    (∀ v ∈ Icc 0 T, ‖derivWithin h (Icc 0 T) v‖ ≤ D) →
    datumVar h T ≤ 1 / 64 → |e| * datumM h T * T ≤ 1 / 16 →
        ∃ ball : ContinuationPicardBall e 0 a T (fun _ => 1 / 2) h
          (1 / 128) (1 / 2 - 1 / 128) (3 / 4), ball.coefficient ≤ C

/-- Pending internal project record uniform short-cone input (E5), internal project record:287.
`τ` is chosen after `B,ℓ,|e|` and before signed coupling, cone position,
length and data. Uniformity over both coupling signs is explicit.
No higher datum norm or small derivative hypothesis is present. -/
@[expose] def ContinuationShortPicardInput : Prop :=
  ∀ (B ℓ E : ℝ), 1 ≤ B → 0 < ℓ → 0 ≤ E → ∃ τ : ℝ, 0 < τ ∧
    ∀ e : ℝ, |e| = E → ∀ (c L : ℝ) (lam₀ : ℝ → ℝ) (h₀ : ℝ → ℂ), 0 < L → L ≤ τ →
      ContDiffOn ℝ 1 lam₀ (Icc c (c + L)) →
      ContDiffOn ℝ 1 h₀ (Icc c (c + L)) →
      (∀ v ∈ Icc c (c + L), ℓ ≤ lam₀ v ∧ |lam₀ v| ≤ B ∧ ‖h₀ v‖ ≤ B ∧
        |derivWithin lam₀ (Icc c (c + L)) v| ≤ B ∧
        ‖derivWithin h₀ (Icc c (c + L)) v‖ ≤ B) →
      ∃ Z : ContinuationPair c L L,
        Z.IsFixedPoint e lam₀ h₀ ∧
        Z.InConeBall lam₀ h₀ (min (1 / 128) (ℓ / 4)) ∧
        ∀ p ∈ continuationWedge c L L,
          ℓ / 2 ≤ Z.lam p.1 p.2 ∧
          3 / 4 ≤ 1 - Recon.mu e Z.lam Z.hh p.1 p.2

/-- Pending internal project record C¹ recovery input, internal project record (19)–(34).
Continuous compatible outgoing jets, C¹ data, the exact fixed-point
equations and S1 suffice. The conclusion concerns the C¹ class only.
The positive lower bounds precede the pointwise nondegeneracy premises. -/
@[expose] def ContinuationRecoveryInput : Prop :=
  ∀ (c a L e ℓ κ : ℝ) (lam₀ : ℝ → ℝ) (h₀ : ℝ → ℂ)
      (Z : ContinuationPair c a L),
    0 < a → a ≤ L → 0 < ℓ → 0 < κ →
    ContDiffOn ℝ 1 lam₀ (Icc c (c + L)) →
    ContDiffOn ℝ 1 h₀ (Icc c (c + L)) →
    (∀ p ∈ continuationWedge c a L,
      ℓ ≤ Z.lam p.1 p.2 ∧ κ ≤ 1 - Recon.mu e Z.lam Z.hh p.1 p.2) →
    Z.IsFixedPoint e lam₀ h₀ →
    IsC1Solution e (Recon.toFields e Z.lam Z.hh) (continuationWedge c a L)

/-- Pending internal project record common primary C¹ bound, the C¹ version of internal project
record's
`SmoothC1BoundStmt` and internal project record (44)–(45). Universal thresholds
precede the datum; `B` follows `T,e,h` and is uniform in every positive
constructed apex. Its proof uses only the datum's first derivative. -/
@[expose] def ContinuationC1BoundInput : Prop :=
  ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧
    ∀ (T e : ℝ) (h : ℝ → ℂ), 0 < T → ContDiffOn ℝ 1 h (Icc 0 T) →
      datumVar h T ≤ ε → chargedScale e h T ≤ δ →
      ∃ B : ℝ, 0 < B ∧ ∀ (s : ℝ) (S : Fields), 0 < s → s ≤ T →
        IsC1Solution e S (triangle 0 s) → IsRestartData S h s →
        C1BoundOn S (triangle 0 s) B

end EmcsfAcExtension.Local
