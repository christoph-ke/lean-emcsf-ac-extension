module

public import EmcsfAcExtension.Local.Construction.ContinuationCarrier
import Mathlib.Topology.MetricSpace.Contracting

/-! # Complete canonical Picard balls and their exact updates

This representation-independent object records the entire canonical
closed ball, its genuine metric completeness, and the exact contracting
paper update. Surjectivity on all four value/jet components prevents an
arbitrary invariant subset from replacing the canonical ball. Banach's
theorem then supplies the fixed-point consequence used in continuation.
-/

public section

open Set
open scoped NNReal

namespace EmcsfAcExtension.Local

/-- A complete metric realization of the full canonical outgoing-jet
ball. Its distance is precisely the maximum of the four component sup
distances on the closed wedge. Every compatible canonical-ball pair
has a representative, modulo equality of all four components there.
The update is a self-map with the literal reconstructed values, and
its contraction coefficient has the incoming-width factor `a`.
The fixed lower expansion and gap hold on the entire ball. -/
structure ContinuationPicardBall (e c a L : ℝ) (lam₀ : ℝ → ℝ) (h₀ : ℝ → ℂ)
    (ρ ℓ κ : ℝ) where
  /-- The carrier represents all canonical-ball pairs on the wedge. -/
  Carrier : Type
  /-- The actual maximum-norm metric on the represented canonical ball. -/
  metric : MetricSpace Carrier
  /-- Metric completeness of this canonical closed ball. -/
  complete : @CompleteSpace Carrier metric.toUniformSpace
  /-- The canonical ball is nonempty. -/
  nonempty : Nonempty Carrier
  /-- Compatible continuous values and outgoing jets of a represented point. -/
  state : Carrier → ContinuationPair c a L
  /-- Every represented point belongs to the prescribed canonical ball. -/
  state_ball : ∀ x, (state x).InConeBall lam₀ h₀ ρ
  /-- The fixed entering values hold at every point of the full initial cone. -/
  state_initial : ∀ x, ∀ v ∈ Icc c (c+L),
    (state x).lam c v = lam₀ v ∧ (state x).hh c v = h₀ v
  /-- Every compatible point of the full canonical ball is represented. -/
  represents : ∀ Z : ContinuationPair c a L,
    Z.InConeBall lam₀ h₀ ρ →
    (∀ v ∈ Icc c (c+L), Z.lam c v = lam₀ v ∧ Z.hh c v = h₀ v) →
    ∃ x, ∀ p ∈ continuationWedge c a L,
      (state x).lam p.1 p.2 = Z.lam p.1 p.2 ∧
      (state x).hh p.1 p.2 = Z.hh p.1 p.2 ∧
      (state x).lamV p.1 p.2 = Z.lamV p.1 p.2 ∧
      (state x).hhV p.1 p.2 = Z.hhV p.1 p.2
  /-- The metric is exactly the sup/max metric of all four components. -/
  distance_le_iff : ∀ x y (r : ℝ), 0 ≤ r →
    (@dist Carrier metric.toDist x y ≤ r ↔
      ∀ p ∈ continuationWedge c a L,
        max (max |(state x).lam p.1 p.2-(state y).lam p.1 p.2|
          ‖(state x).hh p.1 p.2-(state y).hh p.1 p.2‖)
          (max |(state x).lamV p.1 p.2-(state y).lamV p.1 p.2|
            ‖(state x).hhV p.1 p.2-(state y).hhV p.1 p.2‖) ≤ r)
  /-- The literal Picard update preserves the entire canonical ball. -/
  update : Carrier → Carrier
  /-- Both updated values are exactly the paper's reconstructed update. -/
  update_exact : ∀ x, ∀ p ∈ continuationWedge c a L,
    Recon.picardLam e (state x).lam (state x).hh c lam₀ p.1 p.2 =
      (state (update x)).lam p.1 p.2 ∧
    Recon.picardH e (state x).lam (state x).hh c h₀ p.1 p.2 =
      (state (update x)).hh p.1 p.2
  /-- A finite coefficient in the incoming-width Lipschitz estimate. -/
  coefficient : ℝ
  /-- The coefficient is positive. -/
  coefficient_pos : 0 < coefficient
  /-- The incoming-width factor makes the actual map contractive. -/
  coefficient_small : a*coefficient < 1
  /-- The full four-component metric satisfies the actual map estimate. -/
  update_lipschitz : ∀ x y,
    @dist Carrier metric.toDist (update x) (update y) ≤
      (a*coefficient)*@dist Carrier metric.toDist x y
  /-- The expansion and inverse-gap margins hold on every candidate. -/
  state_bounds : ∀ x, ∀ p ∈ continuationWedge c a L,
    ℓ ≤ (state x).lam p.1 p.2 ∧
    κ ≤ 1-Recon.mu e (state x).lam (state x).hh p.1 p.2

/-- A genuine complete canonical ball with its exact contractive update
has a compatible fixed point with the prescribed ball and geometric
bounds. This is a proved Banach projection, not another producer input.
The coefficient and ball precede the constructed fixed point. -/
theorem ContinuationPicardBall.exists_fixedPoint
    {e c a L ρ ℓ κ : ℝ} {lam₀ : ℝ → ℝ} {h₀ : ℝ → ℂ}
    (ball : ContinuationPicardBall e c a L lam₀ h₀ ρ ℓ κ) (ha : 0 < a) :
    ∃ Z : ContinuationPair c a L,
      Z.IsFixedPoint e lam₀ h₀ ∧ Z.InConeBall lam₀ h₀ ρ ∧
      ∀ p ∈ continuationWedge c a L,
        ℓ ≤ Z.lam p.1 p.2 ∧ κ ≤ 1-Recon.mu e Z.lam Z.hh p.1 p.2 := by
  let _ := ball.metric
  let _ := ball.complete
  let _ := ball.nonempty
  let q : ℝ≥0 := ⟨a*ball.coefficient, (mul_pos ha ball.coefficient_pos).le⟩
  have hcontract : ContractingWith q ball.update := by
    refine ⟨ball.coefficient_small,?_⟩
    exact LipschitzWith.of_dist_le_mul ball.update_lipschitz
  let x := ContractingWith.fixedPoint ball.update hcontract
  have hx : ball.update x = x := hcontract.fixedPoint_isFixedPt
  refine ⟨ball.state x,?_,ball.state_ball x,ball.state_bounds x⟩
  intro p hp
  simpa only [hx] using ball.update_exact x p hp

end EmcsfAcExtension.Local
