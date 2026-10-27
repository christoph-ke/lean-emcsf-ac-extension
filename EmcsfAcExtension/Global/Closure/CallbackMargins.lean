module

public import EmcsfAcExtension.Global.Closure.Windows
import Mathlib.Tactic

/-! # Retaining the running-to-absorption stop comparison

The cutoff budget calculation uses the same absorption background as strict
improvement. Retain the comparison between the two numerical stops when
choosing them, before any entry or stage data.
Source: `charged_SF_new_version.tex:L4045–L4083`.
-/

public section

open Set Filter Topology

namespace EmcsfAcExtension.Global.Closure

/-- [internal]
The small-entry strict improvement with its numerical comparison retained:
`εrun ≤ εabs`. All constants depend only on the fixed exterior box and
budget-sum coefficient, before every development, entry row and finite
path. This is the same margin choice as the existing small-entry producer;
it retains the bound needed to derive the stopped partial budgets. -/
theorem strict_finite_stops_of_small_entry_with_margin (δ c Λ F ε ρ Csum : ℝ)
    (hbox : ExteriorBox δ c Λ F ε ρ) (hF : 0 < F) (hε : 0 < ε) (hCsum : 0 ≤ Csum) :
    ∃ εabs εrun q A : ℝ, 0 < εabs ∧ 0 < εrun ∧ 0 < q ∧ 0 < A ∧ εrun ≤ εabs ∧
      ∀ (ui e : ℝ) (S : Fields), OriginalData ui e S → SignedTerminalBound ui S →
      ∃ a ∈ Ioo ui 0, ∀ (u₀ u₁ v₀ R₀ εentry K : ℝ) (vb : ℝ → ℝ)
        (N : ℕ) (B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N) (E T : Fin N → ℝ),
      a ≤ u₀ → 0 < N → 0 ≤ εentry → S.r u₀ 0 = R₀ →
      (∀ u ∈ Icc u₀ u₁, ∀ w ∈ Icc u 0, δ ≤ 1 - S.mu u w) →
      BoundaryBudgets S ui u₀ u₁ v₀ ρ vb N B E → (∀ n, 0 < T n) →
      ∀ γ : ∀ n, ClockCylinder S (origDomain ui) (B.radii n) 0 (T n),
      (∀ n, (γ n).U 0 = B.cuts n.castSucc ∧ (γ n).U (T n) = B.cool n) →
      (∀ n, ∀ τ ∈ Icc 0 (T n), vb ((γ n).U τ) = (γ n).V τ) →
      (∀ v ∈ Icc v₀ 0, 2 * c ≤ S.lam u₀ v) →
      cylinderClock S vb u₀ u₁ ≤ K → 2 * K < R₀ / 4 →
      let J := (interactionNorm e S (exteriorDomain ui u₀ u₁ vb) u₀ v₀).toReal
      let V := ∑ n, (curveCovVar e S S.a (γ n).U (γ n).V 0 (T n)).toReal
      let z := Local.sigma e (Interaction.scalarBackground ui R₀ c F εabs S) (2 * R₀)
      FiniteCutoffStops S ui u₀ R₀ vb (fun _ => J) (fun _ => V) δ c Λ F ε εrun u₁ →
      (∑ n, E n) ≤ Csum * (εentry + V ^ 2) →
      (∑ n, Real.sqrt (E n)) ≤ Csum * (Real.sqrt εentry + V) →
      (initialInteraction S u₀ v₀).toReal + εentry + z ≤ q →
      StrictFiniteCutoffStops S ui u₀ R₀ vb (fun _ => J) (fun _ => V) δ c Λ F ε εrun u₁ ∧
        J + V ≤ A * ((initialInteraction S u₀ v₀).toReal + εentry + z) := by
  obtain ⟨εabs, ηabs, A, ηfield, Copt, hεabs, hηabs, hA, hηfield, hCopt, himprove⟩ :=
    strict_finite_stops_of_budgets δ c Λ F ε ρ Csum hbox hF hε hCsum
  obtain ⟨εrun, q, hεrun, hq, hrun, hqa, hqf, hAq, hAqf, hEF, hEf, hOpt⟩ :=
    exists_strict_stopping_margins εabs ηabs A ηfield Copt Csum F
      hεabs hηabs hA hηfield hCopt hCsum hF
  refine ⟨εabs, εrun, q, A, hεabs, hεrun, hq, hA, hrun, ?_⟩
  intro ui e S h hs
  obtain ⟨a, ha, himprove⟩ := himprove ui e S h hs
  refine ⟨a, ha, ?_⟩
  intro u₀ u₁ v₀ R₀ εentry K vb N B E T hau hN he hR hcore hE hT γ hends hgraph
    hentry hclock hclocksmall
  dsimp only
  intro hstop hsum hhalf hsmall
  let J := (interactionNorm e S (exteriorDomain ui u₀ u₁ vb) u₀ v₀).toReal
  let V := ∑ n, (curveCovVar e S S.a (γ n).U (γ n).V 0 (T n)).toReal
  let z := Local.sigma e (Interaction.scalarBackground ui R₀ c F εabs S) (2 * R₀)
  let L := A * ((initialInteraction S u₀ v₀).toReal + εentry + z)
  have hJ : 0 ≤ J := ENNReal.toReal_nonneg
  have hV : 0 ≤ V := Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg)
  have hz : 0 ≤ z := by dsimp [z, Local.sigma]; positivity
  have hD : 0 ≤ (initialInteraction S u₀ v₀).toReal := ENNReal.toReal_nonneg
  have hVrun : V ≤ εrun := by linarith only [hstop.2.2, hJ]
  have hεq : εentry ≤ q := by linarith only [hsmall, hD, hz]
  have hzq : z ≤ q := by linarith only [hsmall, hD, he]
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hLq : L ≤ A * q := mul_le_mul_of_nonneg_left hsmall hA.le
  have hsum' : (∑ n, E n) ≤ Csum * (q + εrun ^ 2) :=
    hsum.trans (mul_le_mul_of_nonneg_left
      (add_le_add hεq ((sq_le_sq₀ hV hεrun.le).mpr hVrun)) hCsum)
  have hopt : Copt * ((∑ n, E n) + L ^ 2 + z) < Real.log 2 := by
    apply lt_of_le_of_lt ?_ hOpt
    exact mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add hsum' ((sq_le_sq₀ hL (by positivity)).mpr hLq)) hzq) hCopt.le
  exact himprove u₀ u₁ v₀ R₀ εentry K εrun vb N B E T hau hN he hrun hR hcore hE
    (hsum'.trans hEF) hT γ hends hgraph hentry hclock hclocksmall hstop hsum hhalf
    (by linarith only [hsmall, hD, hqa]) (hLq.trans_lt hAq) (hsum'.trans hEf)
    (hLq.trans hAqf) (hzq.trans hqf) hopt


end EmcsfAcExtension.Global.Closure
