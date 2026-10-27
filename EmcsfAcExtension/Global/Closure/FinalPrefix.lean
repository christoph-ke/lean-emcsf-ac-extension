module

public import EmcsfAcExtension.Global.Closure.Callback
public import EmcsfAcExtension.Global.Closure.ConnectorGeometry
public import EmcsfAcExtension.Global.Closure.ConnectorExclusion
import Mathlib.Tactic

/-! # Completed finite histories for the stage induction

The induction state contains actual finite boundaries and clock cylinders.
Its variation sequence is the finite history extended by zero; only its
visited values enter the prescribed durations. A later append changes only
the new variation, so all earlier envelopes are preserved.
Source: `charged_SF_new_version.tex:L3899–L3932`, `charged_SF_new_version.tex:L4106–L4115`.
-/

public section

open Set

namespace EmcsfAcExtension.Global.Closure

/-- [internal]
Transport a clock cylinder across equal radius and duration labels.
The two physical coordinate functions are preserved definitionally.
Constants: none. -/
@[expose] def castClockCylinder {S : Fields} {D : Set (ℝ × ℝ)} {R T : ℝ}
    (γ : ClockCylinder S D R 0 T) (R' T' : ℝ) (hR : R' = R) (hT : T' = T) :
    ClockCylinder S D R' 0 T' where
  U := γ.U
  V := γ.V
  c1_U := by simpa only [hT] using γ.c1_U
  c1_V := by simpa only [hT] using γ.c1_V
  mem := by simpa only [hT] using γ.mem
  radius := by simpa only [hR, hT] using γ.radius
  rate_U := by simpa only [hT] using γ.rate_U
  rate_V := by simpa only [hT] using γ.rate_V

/-- [internal]
An actual completed `N`-stage finite history. The graph, boundaries and
clocks are the frozen source objects; the additional fields record the
induction invariants. The finite variation is zero beyond the visited
stages, and no future physical stage is asserted. All parameters are fixed
before the stage index. -/
structure FinalPrefix (S : Fields)
    (ui e a v₀ ρ b₀ H χ C₁ εentry R₀ δ c Λ F εweak εrun : ℝ) (N : ℕ) where
  /-- Last incoming coordinate of the completed history. -/
  endpoint : ℝ
  /-- Its actual finite boundary graph. -/
  graph : ℝ → ℝ
  /-- The literal finite cylinder and connector geometry. -/
  boundary : FiniteBoundary S ui a endpoint v₀ ρ graph N
  /-- Actual cylinder variations, extended by zero after the finite history. -/
  variation : ℕ → ℝ
  /-- The extension carries no future variation data. -/
  variation_zero : ∀ k, N ≤ k → variation k = 0
  /-- Actual completed cylinder durations. -/
  duration : Fin N → ℝ
  /-- Every available cylinder has positive duration. -/
  duration_pos : ∀ n, 0 < duration n
  /-- The actual physical clock cylinders. -/
  cylinders : ∀ n, ClockCylinder S (origDomain ui) (boundary.radii n) 0 (duration n)
  /-- Cylinder coordinates meet the literal finite cuts and cooling endpoints. -/
  ends : ∀ n, (cylinders n).U 0 = boundary.cuts n.castSucc ∧
    (cylinders n).U (duration n) = boundary.cool n
  /-- The cylinder curves lie on the finite boundary graph. -/
  on_graph : ∀ n, ∀ s ∈ Icc 0 (duration n), graph ((cylinders n).U s) = (cylinders n).V s
  /-- The stored variations are the actual full cylinder variations. -/
  variation_eq : ∀ n : Fin N, variation n =
    (curveCovVar e S S.a (cylinders n).U (cylinders n).V 0 (duration n)).toReal
  /-- Exact geometric radius of each cylinder. -/
  radii_eq : ∀ n : Fin N, boundary.radii n = stageRadius ρ b₀ n
  /-- Every completed cylinder reaches its prescribed clock. -/
  duration_eq : ∀ n : Fin N,
    duration n = H * boundary.radii n / energyEnvelope χ C₁ εentry variation n
  /-- The last connector reaches the next exact geometric radius. -/
  endpoint_radius : S.r endpoint (graph endpoint) = stageRadius ρ b₀ N
  /-- Literal strict stops on the whole available history, with its actual norms. -/
  stops : StrictFiniteCutoffStops S ui a R₀ graph
    (fun _ => (interactionNorm e S (exteriorDomain ui a endpoint graph) a v₀).toReal)
    (fun _ => ∑ n, (curveCovVar e S S.a (cylinders n).U (cylinders n).V
      0 (duration n)).toReal) δ c Λ F εweak εrun endpoint

/-- [internal]
Initialize the completed-history induction at the actual proper entry
sphere. There are no cylinders or connectors at stage zero. All numerical
parameters were fixed before the entry; no constants are selected here. -/
theorem initial_final_prefix {S : Fields}
    {ui e a v₀ ρ b₀ H χ C₁ εentry R₀ δ c Λ F εweak εrun : ℝ}
    (hp : (a, v₀) ∈ origDomain ui) (hoff : a < v₀) (hR : S.r a v₀ = b₀)
    (hentry : StrictFiniteCutoffStops S ui a R₀ (fun _ => v₀)
      (fun _ => (initialInteraction S a v₀).toReal) (fun _ => 0)
      δ c Λ F εweak εrun a) :
    Nonempty (FinalPrefix S ui e a v₀ ρ b₀ H χ C₁ εentry R₀ δ c Λ F εweak εrun 0) := by
  refine ⟨{
    endpoint := a
    graph := fun _ => v₀
    boundary := initialBoundary S ui a v₀ ρ hp hoff
    variation := fun _ => 0
    variation_zero := fun _ _ => rfl
    duration := Fin.elim0
    duration_pos := fun n => Fin.elim0 n
    cylinders := fun n => Fin.elim0 n
    ends := fun n => Fin.elim0 n
    on_graph := fun n => Fin.elim0 n
    variation_eq := fun n => Fin.elim0 n
    radii_eq := fun n => Fin.elim0 n
    duration_eq := fun n => Fin.elim0 n
    endpoint_radius := by simpa only [stageRadius, pow_zero, one_mul] using hR
    stops := ?_ }⟩
  simpa only [interactionNorm_initial_cutoff, Finset.univ_eq_empty, Finset.sum_empty] using hentry

/-- [internal]
Dependent choice for completed finite histories. The extension relation is
kept explicit; applications instantiate it with unchanged old cuts, graph,
radii, cylinder functions and variations. Constants: none. -/
theorem coherent_sequence_of_extension {α : ℕ → Type*}
    (R : ∀ n, α n → α (n + 1) → Prop) (x₀ : α 0)
    (hstep : ∀ n (x : α n), ∃ y : α (n + 1), R n x y) :
    ∃ x : ∀ n, α n, x 0 = x₀ ∧ ∀ n, R n (x n) (x (n + 1)) := by
  classical
  choose next hnext using hstep
  let x : ∀ n, α n := fun n => Nat.rec x₀ (fun n y => next n y) n
  exact ⟨x, rfl, fun n => hnext n (x n)⟩

end EmcsfAcExtension.Global.Closure
