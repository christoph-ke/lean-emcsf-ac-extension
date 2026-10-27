module

public import EmcsfAcExtension.Global.Closure.CallbackEstimates
public import EmcsfAcExtension.Global.Closure.CallbackRestriction
import Mathlib.Tactic

/-! # The literal weak-to-strict cutoff callback

Every noninitial cutoff is realized by an actual partial finite history.
Its completed prefix supplies starting energies, then the budget producer
and absorption give strict stops. All numerical witnesses precede entry.
Source: `charged_SF_new_version.tex:L4045–L4106`.
-/

public section

open Set Filter Topology

namespace EmcsfAcExtension.Global.Closure

/-- [internal]
The actual weak-to-strict callback, including cutoffs on an unfinished
cylinder, on a connector, and at the singleton entry. No callback, later
starting energy, partial budget or finite sum is assumed. The only duration
equalities concern completed preceding cylinders. Thresholds depend only
on `δ`; schedule coefficients additionally on `εweak,ρ,χ`; absorption
coefficients additionally on the fixed box. All precede the development,
entry, available finite path and its cutoff. -/
theorem actual_cutoff_callback_of_small_entry (δ : ℝ) (hδ : 0 < δ ∧ δ < 1) :
    ∃ δs ηs : ℝ, 0 < δs ∧ 0 < ηs ∧
      ∀ (εweak ρ χ : ℝ), 0 < εweak → 0 < ρ → (0 < χ ∧ χ < 1) →
      ∃ H C₁ Cbudget Csum : ℝ,
        0 < H ∧ 0 < C₁ ∧ 0 < Cbudget ∧ 0 < Csum ∧
      ∀ (c Λ F : ℝ), ExteriorBox δ c Λ F εweak ρ → 0 < F → F + εweak ≤ δs →
      ∃ εabs εrun q A : ℝ,
        0 < εabs ∧ 0 < εrun ∧ 0 < q ∧ 0 < A ∧ εrun ≤ εabs ∧
      ∀ (ui e : ℝ) (S : Fields), OriginalData ui e S → SignedTerminalBound ui S →
      ∃ alate ∈ Ioo ui 0,
      ∀ (a b v₀ R₀ εentry K : ℝ) (vb : ℝ → ℝ) (σ : ℕ → ℝ) (N : ℕ)
        (B : FiniteBoundary S ui a b v₀ ρ vb N) (T : Fin N → ℝ),
      alate ≤ a → 0 < εentry → S.r a 0 = R₀ →
      (∀ p ∈ origDomain ui, a ≤ p.1 → 0 ≤ S.mu p.1 p.2 ∧ δ ≤ 1 - S.mu p.1 p.2) →
      (∀ n, B.radii n < R₀ / 2) → (∀ n, 0 < T n) →
      (∀ n : Fin N, n.val + 1 < N →
        T n = H * B.radii n / energyEnvelope χ C₁ εentry σ n) →
      ∀ γ : ∀ n, ClockCylinder S (origDomain ui) (B.radii n) 0 (T n),
      (∀ n, (γ n).U 0 = B.cuts n.castSucc ∧ (γ n).U (T n) = B.cool n) →
      (∀ n, ∀ s ∈ Icc 0 (T n), vb ((γ n).U s) = (γ n).V s) →
      (∀ n : Fin N, σ n = (curveCovVar e S S.a (γ n).U (γ n).V 0 (T n)).toReal) →
      cylinderEnergy S (S.r a v₀) a v₀ / S.r a v₀ ≤ εentry →
      (∀ v ∈ Icc v₀ 0, 2 * c ≤ S.lam a v) →
      cylinderClock S vb a b ≤ K → 2 * K < R₀ / 4 →
      let J := fun t => (interactionNorm e S (exteriorDomain ui a t vb) a v₀).toReal
      let Svar := fun t => ∑ n, (curveCovVar e S S.a (γ n).U (γ n).V 0
        (max 0 (min (T n) (cylinderClock S vb (B.cuts n.castSucc) t)))).toReal
      let z := Local.sigma e (Interaction.scalarBackground ui R₀ c F εabs S) (2 * R₀)
      (initialInteraction S a v₀).toReal + εentry + z ≤ q →
      StrictFiniteCutoffStops S ui a R₀ vb J Svar δ c Λ F εweak εrun a →
      (∀ t ∈ Icc a b, FiniteCutoffStops S ui a R₀ vb J Svar δ c Λ F εweak εrun t →
        StrictFiniteCutoffStops S ui a R₀ vb J Svar δ c Λ F εweak εrun t) ∧
      (0 < N → FiniteCutoffStops S ui a R₀ vb J Svar δ c Λ F εweak εrun b →
        let V := ∑ n, (curveCovVar e S S.a (γ n).U (γ n).V 0 (T n)).toReal
        J b + V ≤ A * ((initialInteraction S a v₀).toReal + εentry + z) ∧
        BoundaryBudgets S ui a b v₀ ρ vb N B
          (fun n => stageBudget Cbudget χ C₁ εentry σ n) ∧
        (∑ n : Fin N, stageBudget Cbudget χ C₁ εentry σ n) ≤
          Csum * (εentry + V ^ 2) ∧
        (∑ n : Fin N, Real.sqrt (stageBudget Cbudget χ C₁ εentry σ n)) ≤
          Csum * (Real.sqrt εentry + V)) := by
  obtain ⟨δs, ηs, hδs, hηs, hpartial⟩ := strict_partial_stops_of_small_entry δ hδ
  refine ⟨δs, ηs, hδs, hηs, ?_⟩
  intro εweak ρ χ hεweak hρ hχ
  obtain ⟨H, C₁, Cb, Csum, hH, hC₁, hCb, hCsum, hboxes⟩ :=
    hpartial εweak ρ χ hεweak hρ hχ
  refine ⟨H, C₁, Cb, Csum, hH, hC₁, hCb, hCsum, ?_⟩
  intro c Λ F hbox hF hweak
  obtain ⟨εabs, εrun, q, A, hεabs, hεrun, hq, hA, hrun, hdata⟩ := hboxes c Λ F hbox hF hweak
  refine ⟨εabs, εrun, q, A, hεabs, hεrun, hq, hA, hrun, ?_⟩
  intro ui e S h hs
  obtain ⟨alate, halate, himprove⟩ := hdata ui e S h hs
  refine ⟨alate, halate, ?_⟩
  intro a b v₀ R₀ εentry K vb σ N B T halate_a he hR₀ hgap hRn hT hcomplete
    γ hends hgraph hσ henergy hentrylam hclock hclocksmall
  dsimp only
  intro hsmall hentry
  constructor
  · intro t ht hstop
    by_cases hta : t = a
    · simpa only [hta] using hentry
    have hat : a < t := lt_of_le_of_ne ht.1 (Ne.symm hta)
    obtain ⟨M, hMN, hM, B', T', γ', hcuts, hradii, hshort, hprev, hcurves,
      hends', hgraph', hvar⟩ := finite_cutoff_realization h B T hT γ hends hgraph ⟨hat, ht.2⟩
    let σ' : ℕ → ℝ := fun k => if hk : k < M then
      (curveCovVar e S S.a (γ' ⟨k, hk⟩).U (γ' ⟨k, hk⟩).V 0 (T' ⟨k, hk⟩)).toReal else 0
    have hσ' (i : Fin M) : σ' i =
        (curveCovVar e S S.a (γ' i).U (γ' i).V 0 (T' i)).toReal := by
      simp only [σ', dite_eq_left i.isLt]
    have hbefore (k : ℕ) (hk : k + 1 < M) : σ' k = σ k := by
      let i : Fin M := ⟨k, by omega⟩
      rw [hσ' i, (hcurves i).1, (hcurves i).2, hprev i hk, ← hσ (i.castLE hMN)]
      rfl
    have henv (i : Fin M) : energyEnvelope χ C₁ εentry σ' i =
        energyEnvelope χ C₁ εentry σ i := by
      apply energyEnvelope_congr_before
      intro k hk
      exact hbefore k (by have hi := i.isLt; omega)
    have hcomplete' (i : Fin M) (hi : i.val + 1 < M) :
        T' i = H * B'.radii i / energyEnvelope χ C₁ εentry σ' i := by
      rw [hprev i hi, hradii i, henv i]
      exact hcomplete (i.castLE hMN) (by simpa only [Fin.val_castLE] using hi.trans_le hMN)
    have hab : a ≤ b := ht.1.trans ht.2
    have hclock' : cylinderClock S vb a t ≤ K :=
      (monotoneOn_cylinderClock h B ⟨le_rfl, hab⟩ ht ⟨hab, le_rfl⟩ ht.2).trans hclock
    have hstop' : FiniteCutoffStops S ui a R₀ vb
        (fun _ => (interactionNorm e S (exteriorDomain ui a t vb) a v₀).toReal)
        (fun _ => ∑ n, (curveCovVar e S S.a (γ' n).U (γ' n).V 0 (T' n)).toReal)
        δ c Λ F εweak εrun t := by
      simpa only [FiniteCutoffStops, hvar] using hstop
    obtain ⟨hstrict, _⟩ := himprove a t v₀ R₀ εentry K vb σ' M B' T'
      halate_a hM he hR₀ hgap (fun i => (hradii i).symm ▸ hRn (i.castLE hMN))
      (fun i => (hshort i).1) hcomplete' γ' hends' hgraph' hσ' henergy hentrylam
      hclock' hclocksmall hstop' hsmall
    simpa only [StrictFiniteCutoffStops, hvar] using hstrict
  · intro hN hstop
    have hvar := clipped_variation_final h B T (fun n => (hT n).le) γ hends hgraph
    have hstop' : FiniteCutoffStops S ui a R₀ vb
        (fun _ => (interactionNorm e S (exteriorDomain ui a b vb) a v₀).toReal)
        (fun _ => ∑ n, (curveCovVar e S S.a (γ n).U (γ n).V 0 (T n)).toReal)
        δ c Λ F εweak εrun b := by
      simpa only [FiniteCutoffStops, hvar] using hstop
    exact (himprove a b v₀ R₀ εentry K vb σ N B T halate_a hN he hR₀ hgap hRn hT
      hcomplete γ hends hgraph hσ henergy hentrylam hclock hclocksmall hstop' hsmall).2

end EmcsfAcExtension.Global.Closure
