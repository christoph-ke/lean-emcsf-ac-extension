module

public import EmcsfAcExtension.Global.Closure.CallbackEnergy
public import EmcsfAcExtension.Global.Closure.CallbackMargins
import Mathlib.Tactic

/-! # Strict improvement from the completed prefix's entry energy

Fix the recurrence, budget and absorption coefficients once. On each
restricted finite cutoff, produce its starting energies and actual partial
budgets before invoking the small-entry strict improvement.
Source: `charged_SF_new_version.tex:L3908–L3928`, `charged_SF_new_version.tex:L4045–L4083`.
-/

public section

open Set Filter Topology

namespace EmcsfAcExtension.Global.Closure

/-- [internal]
Choose all coefficients before entry data. Every nonempty available finite
path with an arbitrary partial last cylinder has strict stopping improvement
from entry energy alone. Earlier cylinders have their prescribed durations.
The actual budgets, their two sums, and every later starting energy are
derived inside the proof. The running stop is below the fixed absorption
stop, and the quantitative closed interaction estimate is retained.
The thresholds depend only on `δ`; schedule coefficients additionally on
`εweak,ρ,χ`; absorption coefficients additionally on the fixed exterior box.
All precede the development, entry energy, entry row and stage cutoff. -/
theorem strict_partial_stops_of_small_entry (δ : ℝ) (hδ : 0 < δ ∧ δ < 1) :
    ∃ δs ηs : ℝ, 0 < δs ∧ 0 < ηs ∧
      ∀ (εweak ρ χ : ℝ), 0 < εweak → 0 < ρ → (0 < χ ∧ χ < 1) →
      ∃ H C₁ Cbudget Csum : ℝ,
        0 < H ∧ 0 < C₁ ∧ 0 < Cbudget ∧ 0 < Csum ∧
      ∀ (c Λ F : ℝ), ExteriorBox δ c Λ F εweak ρ → 0 < F →
      F + εweak ≤ δs →
      ∃ εabs εrun q A : ℝ,
        0 < εabs ∧ 0 < εrun ∧ 0 < q ∧ 0 < A ∧ εrun ≤ εabs ∧
      ∀ (ui e : ℝ) (S : Fields), OriginalData ui e S → SignedTerminalBound ui S →
      ∃ alate ∈ Ioo ui 0,
      ∀ (a b v₀ R₀ εentry K : ℝ) (vb : ℝ → ℝ) (σ : ℕ → ℝ) (N : ℕ)
        (B : FiniteBoundary S ui a b v₀ ρ vb N) (T : Fin N → ℝ),
      alate ≤ a → 0 < N → 0 < εentry → S.r a 0 = R₀ →
      (∀ p ∈ origDomain ui, a ≤ p.1 → 0 ≤ S.mu p.1 p.2 ∧ δ ≤ 1 - S.mu p.1 p.2) →
      (∀ n, B.radii n < R₀ / 2) → (∀ n, 0 < T n) →
      (∀ n : Fin N, n.val + 1 < N →
        T n = H * B.radii n / energyEnvelope χ C₁ εentry σ n) →
      ∀ γ : ∀ n, ClockCylinder S (origDomain ui) (B.radii n) 0 (T n),
      (∀ n, (γ n).U 0 = B.cuts n.castSucc ∧ (γ n).U (T n) = B.cool n) →
      (∀ n, ∀ τ ∈ Icc 0 (T n), vb ((γ n).U τ) = (γ n).V τ) →
      (∀ n : Fin N, σ n = (curveCovVar e S S.a (γ n).U (γ n).V 0 (T n)).toReal) →
      cylinderEnergy S (S.r a v₀) a v₀ / S.r a v₀ ≤ εentry →
      (∀ v ∈ Icc v₀ 0, 2 * c ≤ S.lam a v) →
      cylinderClock S vb a b ≤ K → 2 * K < R₀ / 4 →
      let J := (interactionNorm e S (exteriorDomain ui a b vb) a v₀).toReal
      let V := ∑ n : Fin N, (curveCovVar e S S.a (γ n).U (γ n).V 0 (T n)).toReal
      let z := Local.sigma e (Interaction.scalarBackground ui R₀ c F εabs S) (2 * R₀)
      FiniteCutoffStops S ui a R₀ vb (fun _ => J) (fun _ => V)
        δ c Λ F εweak εrun b →
      (initialInteraction S a v₀).toReal + εentry + z ≤ q →
      StrictFiniteCutoffStops S ui a R₀ vb (fun _ => J) (fun _ => V)
        δ c Λ F εweak εrun b ∧
        J + V ≤ A * ((initialInteraction S a v₀).toReal + εentry + z) ∧
        BoundaryBudgets S ui a b v₀ ρ vb N B
          (fun n => stageBudget Cbudget χ C₁ εentry σ n) ∧
        (∑ n : Fin N, stageBudget Cbudget χ C₁ εentry σ n) ≤
          Csum * (εentry + V ^ 2) ∧
        (∑ n : Fin N, Real.sqrt (stageBudget Cbudget χ C₁ εentry σ n)) ≤
          Csum * (Real.sqrt εentry + V) := by
  obtain ⟨δs, ηs, hδs, hηs, hpartial⟩ := stopped_partial_budgets δ hδ
  refine ⟨δs, ηs, hδs, hηs, ?_⟩
  intro εweak ρ χ hεweak hρ hχ
  obtain ⟨H, C₁, Cb, Csum, hH, hC₁, hCb, hCsum, hbudgets⟩ :=
    hpartial εweak ρ χ hεweak.le hρ hχ
  refine ⟨H, C₁, Cb, Csum, hH, hC₁, hCb, hCsum, ?_⟩
  intro c Λ F hbox hF hweak
  obtain ⟨εabs, εrun, q, A, hεabs, hεrun, hq, hA, hrun, hstrict⟩ :=
    strict_finite_stops_of_small_entry_with_margin δ c Λ F εweak ρ Csum
      hbox hF hεweak hCsum.le
  let q' := min q (min 1 (ηs ^ 2 / 9))
  have hq' : 0 < q' := by dsimp [q']; positivity
  refine ⟨εabs, εrun, q', A, hεabs, hεrun, hq', hA, hrun, ?_⟩
  intro ui e S h hs
  obtain ⟨alate, halate, himprove⟩ := hstrict ui e S h hs
  refine ⟨alate, halate, ?_⟩
  intro a b v₀ R₀ εentry K vb σ N B T halate_a hN he hR₀ hgap hRn hT hcomplete
    γ hends hgraph hσ hentry hentrylam hclock hclocksmall
  dsimp only
  intro hstop hsmall
  let J := (interactionNorm e S (exteriorDomain ui a b vb) a v₀).toReal
  let V := ∑ n : Fin N, (curveCovVar e S S.a (γ n).U (γ n).V 0 (T n)).toReal
  let z := Local.sigma e (Interaction.scalarBackground ui R₀ c F εabs S) (2 * R₀)
  have hV : 0 ≤ V := Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg)
  have hJrun : J ≤ εrun := by linarith only [hstop.2.2, hV]
  have hJ : J ≤ εabs := hJrun.trans hrun
  have hz : z ≤ q' := by
    have hD : 0 ≤ (initialInteraction S a v₀).toReal := ENNReal.toReal_nonneg
    linarith only [hsmall, hD, he]
  have hz1 : z ≤ 1 := hz.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hzη : 9 * z ≤ ηs ^ 2 := by
    have hh : z ≤ ηs ^ 2 / 9 := hz.trans ((min_le_right _ _).trans (min_le_right _ _))
    linarith only [hh]
  obtain ⟨hbud, hsum, hhalf⟩ := hbudgets ui e a b v₀ R₀ c Λ F εabs εentry S vb σ N B T
    h hbox hεabs.le he hweak hstop.1 hR₀ hstop.2.1 hJ hgap hRn (fun n => (hT n).le)
    hcomplete γ hends hgraph hσ hentry hz1 hzη
  have hσsum : (∑ n : Fin N, σ n) = V := by
    apply Finset.sum_congr rfl
    intro n _
    exact hσ n
  rw [hσsum] at hsum hhalf
  have hresult := himprove a b v₀ R₀ εentry K vb N B
    (fun n => stageBudget Cb χ C₁ εentry σ n) T halate_a hN he.le hR₀
    (fun u hu w hw => (hgap (u, w)
      ⟨(B.mem u hu).1, (B.mem u hu).2.1, hw.1, hw.2⟩ hu.1).2)
    hbud hT γ hends hgraph hentrylam hclock hclocksmall hstop hsum hhalf
    (hsmall.trans (min_le_left _ _))
  exact ⟨hresult.1, hresult.2, hbud, hsum, hhalf⟩

end EmcsfAcExtension.Global.Closure
