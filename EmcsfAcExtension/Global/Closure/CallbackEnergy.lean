module

public import EmcsfAcExtension.Global.Closure.ConnectorEnergy
public import EmcsfAcExtension.Global.Closure.Absorption
import Mathlib.Tactic

/-! # Starting energies on a partial last cylinder

Only completed cylinders enter the recurrence. In particular, the current
cylinder's prescribed duration is never inferred from its capped duration.
The resulting starting energies supply the actual stopped budget producer.
Source: `charged_SF_new_version.tex:L3908–L3928`.
-/

public section

open Set

namespace EmcsfAcExtension.Global.Closure

/-- [internal]
Propagate every cylinder's starting energy from the entry energy on a
finite path whose last cylinder may be unfinished. All preceding cylinders
have their prescribed durations; no recurrence is applied to the last one.
The thresholds depend only on `δ`, and `H,C₁` only on `δ,εweak,ρ,χ`,
before physical data, entry energy, variations and finite cutoff. -/
theorem stopped_starting_energies (δ : ℝ) (hδ : 0 < δ ∧ δ < 1) :
    ∃ Ts δs ηs : ℝ, 0 < Ts ∧ 0 < δs ∧ 0 < ηs ∧
      ∀ (εweak ρ χ : ℝ), 0 ≤ εweak → 0 < ρ → 0 < χ →
      ∃ H C₁ : ℝ, 0 < H ∧ 0 < C₁ ∧
      ∀ (ui e a b v₀ R₀ c Λ F Jstop εentry : ℝ) (S : Fields)
        (vb : ℝ → ℝ) (σ : ℕ → ℝ) (N : ℕ)
        (B : FiniteBoundary S ui a b v₀ ρ vb N) (T : Fin N → ℝ),
      OriginalData ui e S → ExteriorBox δ c Λ F εweak ρ → 0 ≤ Jstop → 0 < εentry →
      F + εweak ≤ δs → ExteriorStops S (exteriorDomain ui a b vb) δ c Λ F εweak →
      S.r a 0 = R₀ → (∀ u ∈ Icc a b, R₀ / 2 ≤ S.r u 0) →
      (interactionNorm e S (exteriorDomain ui a b vb) a v₀).toReal ≤ Jstop →
      (∀ p ∈ origDomain ui, a ≤ p.1 → 0 ≤ S.mu p.1 p.2 ∧ δ ≤ 1 - S.mu p.1 p.2) →
      (∀ n, B.radii n < R₀ / 2) → (∀ n, 0 ≤ T n) →
      (∀ n : Fin N, n.val + 1 < N →
        T n = H * B.radii n / energyEnvelope χ C₁ εentry σ n) →
      ∀ γ : ∀ n, ClockCylinder S (origDomain ui) (B.radii n) 0 (T n),
      (∀ n, (γ n).U 0 = B.cuts n.castSucc ∧ (γ n).U (T n) = B.cool n) →
      (∀ n, ∀ τ ∈ Icc 0 (T n), vb ((γ n).U τ) = (γ n).V τ) →
      (∀ n : Fin N, σ n = (curveCovVar e S S.a (γ n).U (γ n).V 0 (T n)).toReal) →
      cylinderEnergy S (S.r a v₀) a v₀ / S.r a v₀ ≤ εentry →
      let z := Local.sigma e (Interaction.scalarBackground ui R₀ c F Jstop S) (2 * R₀)
      z ≤ 1 → 9 * z ≤ ηs ^ 2 →
      ∀ n, cylinderEnergy S (B.radii n) ((γ n).U 0) ((γ n).V 0) / B.radii n ≤
        energyEnvelope χ C₁ εentry σ n := by
  obtain ⟨Ts, δs, ηs, hTs, hδs, hηs, hsteps⟩ := stopped_connector_recurrence δ hδ
  refine ⟨Ts, δs, ηs, hTs, hδs, hηs, ?_⟩
  intro εweak ρ χ hεweak hρ hχ
  obtain ⟨H, C₁, hH, hC₁, hstep⟩ := hsteps εweak ρ χ hεweak hρ hχ
  refine ⟨H, C₁, hH, hC₁, ?_⟩
  intro ui e a b v₀ R₀ c Λ F Jstop εentry S vb σ N B T
    h hbox hJstop he hweak hstop hR₀ hretained hJ hgap hRn hT hcomplete
    γ hends hgraph hσ hentry
  dsimp only
  intro hz1 hzη
  let E := energyEnvelope χ C₁ εentry σ
  let q := fun i : Fin (N + 1) =>
    cylinderEnergy S (S.r (B.cuts i) (vb (B.cuts i)))
      (B.cuts i) (vb (B.cuts i)) / S.r (B.cuts i) (vb (B.cuts i))
  have hEp (n : ℕ) : 0 < E n := energyEnvelope_pos hχ hC₁.le he σ n
  have hstart (n : Fin N) :
      q n.castSucc = cylinderEnergy S (B.radii n) ((γ n).U 0) ((γ n).V 0) / B.radii n := by
    have hr := B.cylinder n (B.cuts n.castSucc) ⟨le_rfl, (B.split n).1⟩
    simp only [q, ← hgraph n 0 (left_mem_Icc.mpr (hT n)), (hends n).1, hr]
  have hcut : ∀ i : Fin (N + 1), i.val < N → q i ≤ E i := by
    intro i
    induction i using Fin.induction with
    | zero =>
      intro _
      simpa only [q, B.first, B.entry_label, E, Fin.val_zero, energyEnvelope_zero] using hentry
    | @succ n ih =>
      intro hn
      have hprev := ih (by simpa only [Fin.val_castSucc] using Nat.lt_of_succ_lt hn)
      have hen : cylinderEnergy S (B.radii n) ((γ n).U 0) ((γ n).V 0) / B.radii n ≤ E n := by
        simpa only [hstart, Fin.val_castSucc] using hprev
      have hc := hcomplete n hn
      have hrec := hstep ui e a b v₀ R₀ c Λ F Jstop (E n) S vb N B n
        h hbox hJstop (hEp n) hweak hstop hR₀ hretained hJ hgap (hRn n)
      have hbound : q n.succ ≤ χ * E n + C₁ *
          (curveCovVar e S S.a (γ n).U (γ n).V 0 (T n)).toReal ^ 2 := by
        rw [← hc] at hrec
        exact hrec (γ n) (hends n) (hgraph n) hen hz1 hzη
          (B.cuts n.succ) ⟨(B.split n).2, le_rfl⟩
      change q n.succ ≤ energyEnvelope χ C₁ εentry σ (n.val + 1)
      rw [energyEnvelope_succ]
      simpa only [E, ← hσ n] using hbound
  intro n
  simpa only [← hstart n, Fin.val_castSucc] using hcut n.castSucc n.isLt

/-- [internal]
On a stopped partial-stage path, derive the actual boundary budgets and
both finite sums from entry energy alone. The current duration is arbitrary;
every earlier duration is prescribed. The thresholds precede the weak
box, and all four coefficients precede every field, scale and cutoff.
No later starting energy, connector budget or finite sum is assumed. -/
theorem stopped_partial_budgets (δ : ℝ) (hδ : 0 < δ ∧ δ < 1) :
    ∃ δs ηs : ℝ, 0 < δs ∧ 0 < ηs ∧
      ∀ (εweak ρ χ : ℝ), 0 ≤ εweak → 0 < ρ → (0 < χ ∧ χ < 1) →
      ∃ H C₁ Cbudget Csum : ℝ,
        0 < H ∧ 0 < C₁ ∧ 0 < Cbudget ∧ 0 < Csum ∧
      ∀ (ui e a b v₀ R₀ c Λ F Jstop εentry : ℝ) (S : Fields)
        (vb : ℝ → ℝ) (σ : ℕ → ℝ) (N : ℕ)
        (B : FiniteBoundary S ui a b v₀ ρ vb N) (T : Fin N → ℝ),
      OriginalData ui e S → ExteriorBox δ c Λ F εweak ρ → 0 ≤ Jstop → 0 < εentry →
      F + εweak ≤ δs → ExteriorStops S (exteriorDomain ui a b vb) δ c Λ F εweak →
      S.r a 0 = R₀ → (∀ u ∈ Icc a b, R₀ / 2 ≤ S.r u 0) →
      (interactionNorm e S (exteriorDomain ui a b vb) a v₀).toReal ≤ Jstop →
      (∀ p ∈ origDomain ui, a ≤ p.1 → 0 ≤ S.mu p.1 p.2 ∧ δ ≤ 1 - S.mu p.1 p.2) →
      (∀ n, B.radii n < R₀ / 2) → (∀ n, 0 ≤ T n) →
      (∀ n : Fin N, n.val + 1 < N →
        T n = H * B.radii n / energyEnvelope χ C₁ εentry σ n) →
      ∀ γ : ∀ n, ClockCylinder S (origDomain ui) (B.radii n) 0 (T n),
      (∀ n, (γ n).U 0 = B.cuts n.castSucc ∧ (γ n).U (T n) = B.cool n) →
      (∀ n, ∀ τ ∈ Icc 0 (T n), vb ((γ n).U τ) = (γ n).V τ) →
      (∀ n : Fin N, σ n = (curveCovVar e S S.a (γ n).U (γ n).V 0 (T n)).toReal) →
      cylinderEnergy S (S.r a v₀) a v₀ / S.r a v₀ ≤ εentry →
      let z := Local.sigma e (Interaction.scalarBackground ui R₀ c F Jstop S) (2 * R₀)
      z ≤ 1 → 9 * z ≤ ηs ^ 2 →
      let E := fun n : Fin N => stageBudget Cbudget χ C₁ εentry σ n
      let V := ∑ n : Fin N, σ n
      BoundaryBudgets S ui a b v₀ ρ vb N B E ∧
        (∑ n, E n) ≤ Csum * (εentry + V ^ 2) ∧
        (∑ n, Real.sqrt (E n)) ≤ Csum * (Real.sqrt εentry + V) := by
  obtain ⟨_, δe, ηe, _, hδe, hηe, henergies⟩ := stopped_starting_energies δ hδ
  obtain ⟨_, δb, ηb, _, hδb, hηb, hbudgets⟩ :=
    stopped_boundary_budgets_of_initial_energies δ hδ
  refine ⟨min δe δb, min ηe ηb, lt_min hδe hδb, lt_min hηe hηb, ?_⟩
  intro εweak ρ χ hεweak hρ hχ
  obtain ⟨H, C₁, hH, hC₁, henergy⟩ := henergies εweak ρ χ hεweak hρ hχ.1
  obtain ⟨Cb, hCb, hbudget⟩ := hbudgets εweak ρ hεweak hρ
  obtain ⟨Csum, hCsum, hsum⟩ := cc_budget_sums χ C₁ Cb ⟨hχ.1.le, hχ.2⟩ hC₁.le hCb.le
  refine ⟨H, C₁, Cb, Csum, hH, hC₁, hCb, hCsum, ?_⟩
  intro ui e a b v₀ R₀ c Λ F Jstop εentry S vb σ N B T
    h hbox hJstop he hweak hstop hR₀ hretained hJ hgap hRn hT hcomplete
    γ hends hgraph hσ hentry
  dsimp only
  intro hz1 hzη
  have hηe' : 9 * Local.sigma e
      (Interaction.scalarBackground ui R₀ c F Jstop S) (2 * R₀) ≤ ηe ^ 2 :=
    hzη.trans ((sq_le_sq₀ (le_of_lt (lt_min hηe hηb)) hηe.le).mpr (min_le_left _ _))
  have hηb' : 9 * Local.sigma e
      (Interaction.scalarBackground ui R₀ c F Jstop S) (2 * R₀) ≤ ηb ^ 2 :=
    hzη.trans ((sq_le_sq₀ (le_of_lt (lt_min hηe hηb)) hηb.le).mpr (min_le_right _ _))
  have hstart := henergy ui e a b v₀ R₀ c Λ F Jstop εentry S vb σ N B T
    h hbox hJstop he (hweak.trans (min_le_left _ _)) hstop hR₀ hretained hJ hgap
    hRn hT hcomplete γ hends hgraph hσ hentry hz1 hηe'
  have hb := hbudget χ C₁ εentry c Λ F ui e a b v₀ Jstop R₀ S vb σ N B T
    hχ.1.le hC₁.le he.le hJstop (hweak.trans (min_le_right _ _))
    h hbox hstop hR₀ hretained hJ hgap hRn hT γ hends hgraph hσ hstart hz1 hηb'
  have hs (n : ℕ) (hn : n < N) : 0 ≤ σ n := by
    rw [hσ ⟨n, hn⟩]
    exact ENNReal.toReal_nonneg
  have hsum' := hsum εentry σ N he.le hs
  rw [Finset.sum_range, Finset.sum_range, Finset.sum_range] at hsum'
  exact ⟨hb, hsum'⟩

end EmcsfAcExtension.Global.Closure
