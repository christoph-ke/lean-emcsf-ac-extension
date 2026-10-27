module

public import EmcsfAcExtension.Global.Closure.CallbackVariation
import EmcsfAcExtension.Global.Observation.CylinderClock
import Mathlib.Tactic

/-! # Actual clock families on partial last stages

Restrict the available last cylinder, or its connector, on the same
boundary graph. The sum of these actual variations is precisely the
literal clipped variation. No schedule-completion assertion enters here.
Source: `charged_SF_new_version.tex:L3919–L3929`, `charged_SF_new_version.tex:L4104–L4106`.
-/

public section

open Set

namespace EmcsfAcExtension.Global.Closure

/-- [internal]
An interior cutoff on the last cylinder gives an actual finite boundary
with positive clock durations. All earlier clocks, all starting cuts and
all radii are preserved. The literal clipped variation equals the sum on
the restricted clocks. Constants: none. -/
theorem last_cylinder_cutoff_path {ui e a b v₀ ρ : ℝ} {S : Fields}
    (h : OriginalData ui e S) {vb : ℝ → ℝ} {N : ℕ}
    (B : FiniteBoundary S ui a b v₀ ρ vb (N + 1))
    (T : Fin (N + 1) → ℝ) (hT : ∀ n, 0 < T n)
    (γ : ∀ n, ClockCylinder S (origDomain ui) (B.radii n) 0 (T n))
    (hends : ∀ n, (γ n).U 0 = B.cuts n.castSucc ∧ (γ n).U (T n) = B.cool n)
    (hgraph : ∀ n, ∀ s ∈ Icc 0 (T n), vb ((γ n).U s) = (γ n).V s)
    {τ : ℝ} (hτ : τ ∈ Ioc 0 (T (Fin.last N))) :
    ∃ B' : FiniteBoundary S ui a ((γ (Fin.last N)).U τ) v₀ ρ vb (N + 1),
    ∃ T' : Fin (N + 1) → ℝ,
    ∃ γ' : ∀ n, ClockCylinder S (origDomain ui) (B'.radii n) 0 (T' n),
      (∀ n : Fin (N + 1), B'.cuts n.castSucc = B.cuts n.castSucc) ∧
      (∀ n, B'.radii n = B.radii n) ∧
      (∀ n, 0 < T' n ∧ T' n ≤ T n) ∧
      (∀ n : Fin N, T' n.castSucc = T n.castSucc) ∧
      (∀ n, (γ' n).U = (γ n).U ∧ (γ' n).V = (γ n).V) ∧
      (∀ n, (γ' n).U 0 = B'.cuts n.castSucc ∧ (γ' n).U (T' n) = B'.cool n) ∧
      (∀ n, ∀ s ∈ Icc 0 (T' n), vb ((γ' n).U s) = (γ' n).V s) ∧
      (∑ n, (curveCovVar e S S.a (γ n).U (γ n).V 0
        (max 0 (min (T n) (cylinderClock S vb (B.cuts n.castSucc)
          ((γ (Fin.last N)).U τ))))).toReal) =
        ∑ n, (curveCovVar e S S.a (γ' n).U (γ' n).V 0 (T' n)).toReal := by
  let x := (γ (Fin.last N)).U τ
  have hm := ((γ (Fin.last N)).strictMonoOn_U h.solution).monotoneOn
  have hxlow : B.cuts (Fin.last N).castSucc ≤ x := by
    simpa only [(hends _).1] using hm ⟨le_rfl, (hT _).le⟩
      ⟨hτ.1.le, hτ.2⟩ hτ.1.le
  have hxcool : x ≤ B.cool (Fin.last N) := by
    simpa only [(hends _).2] using hm ⟨hτ.1.le, hτ.2⟩
      ⟨(hT _).le, le_rfl⟩ hτ.2
  have hxb : x ≤ b := hxcool.trans ((B.split _).2.trans
    ((B.ordered (Fin.le_last _)).trans B.last.le))
  let B' := cutLastBoundary B x ⟨hxlow, hxb⟩
  let T' : Fin (N + 1) → ℝ := Fin.lastCases τ (fun n => T n.castSucc)
  have hshort (n : Fin (N + 1)) : 0 < T' n ∧ T' n ≤ T n := by
    refine Fin.lastCases ?_ (fun j => ?_) n
    · simpa only [T', Fin.lastCases_last] using And.intro hτ.1 hτ.2
    · simpa only [T', Fin.lastCases_castSucc] using And.intro (hT j.castSucc) le_rfl
  let γ' : ∀ n, ClockCylinder S (origDomain ui) (B'.radii n) 0 (T' n) :=
    fun n => restrictClockCylinder (γ n) 0 (T' n) le_rfl (hshort n).2
  refine ⟨B', T', γ', ?_, (fun _ => rfl), hshort, ?_,
    (fun _ => ⟨rfl, rfl⟩), ?_, ?_, ?_⟩
  · intro n
    change Fin.lastCases (motive := fun _ : Fin (N + 2) => ℝ) x
      (fun i : Fin (N + 1) => B.cuts i.castSucc) n.castSucc = B.cuts n.castSucc
    exact Fin.lastCases_castSucc n
  · intro n
    exact Fin.lastCases_castSucc _
  · intro n
    refine ⟨?_, ?_⟩
    · change (γ n).U 0 = Fin.lastCases x (fun i => B.cuts i.castSucc) n.castSucc
      rw [Fin.lastCases_castSucc]
      exact (hends n).1
    · change (γ n).U (T' n) =
        Fin.lastCases (min (B.cool (Fin.last N)) x) (fun i => B.cool i.castSucc) n
      refine Fin.lastCases ?_ (fun j => ?_) n
      · simp only [T', Fin.lastCases_last, min_eq_right hxcool]
        rfl
      · simpa only [T', Fin.lastCases_castSucc] using (hends j.castSucc).2
  · intro n s hs
    exact hgraph n s ⟨hs.1, hs.2.trans (hshort n).2⟩
  · rw [cutoff_variation_on_last_cylinder h B T hT γ hends hgraph ⟨hτ.1.le, hτ.2⟩]
    rw [Fin.sum_univ_castSucc]
    simp only [γ', restrictClockCylinder_U, restrictClockCylinder_V,
      T', Fin.lastCases_castSucc, Fin.lastCases_last]

/-- [internal]
A cutoff on the last connector preserves every full cylinder clock.
Only the connector endpoint is shortened. The accumulated literal
variation is exactly the sum of the full cylinder variations.
Constants: none. -/
theorem last_connector_cutoff_path {ui e a b v₀ ρ : ℝ} {S : Fields}
    (h : OriginalData ui e S) {vb : ℝ → ℝ} {N : ℕ}
    (B : FiniteBoundary S ui a b v₀ ρ vb (N + 1))
    (T : Fin (N + 1) → ℝ) (hT : ∀ n, 0 ≤ T n)
    (γ : ∀ n, ClockCylinder S (origDomain ui) (B.radii n) 0 (T n))
    (hends : ∀ n, (γ n).U 0 = B.cuts n.castSucc ∧ (γ n).U (T n) = B.cool n)
    (hgraph : ∀ n, ∀ s ∈ Icc 0 (T n), vb ((γ n).U s) = (γ n).V s)
    {x : ℝ} (hx : x ∈ Icc (B.cool (Fin.last N)) b) :
    ∃ B' : FiniteBoundary S ui a x v₀ ρ vb (N + 1),
    ∃ γ' : ∀ n, ClockCylinder S (origDomain ui) (B'.radii n) 0 (T n),
      (∀ n : Fin (N + 1), B'.cuts n.castSucc = B.cuts n.castSucc) ∧
      (∀ n, B'.radii n = B.radii n) ∧
      (∀ n, (γ' n).U = (γ n).U ∧ (γ' n).V = (γ n).V) ∧
      (∀ n, (γ' n).U 0 = B'.cuts n.castSucc ∧ (γ' n).U (T n) = B'.cool n) ∧
      (∀ n, ∀ s ∈ Icc 0 (T n), vb ((γ' n).U s) = (γ' n).V s) ∧
      (∑ n, (curveCovVar e S S.a (γ n).U (γ n).V 0
        (max 0 (min (T n) (cylinderClock S vb (B.cuts n.castSucc) x)))).toReal) =
        ∑ n, (curveCovVar e S S.a (γ' n).U (γ' n).V 0 (T n)).toReal := by
  let B' := cutLastBoundary B x ⟨(B.split _).1.trans hx.1, hx.2⟩
  let γ' : ∀ n, ClockCylinder S (origDomain ui) (B'.radii n) 0 (T n) := γ
  refine ⟨B', γ', ?_,
    (fun _ => rfl), (fun _ => ⟨rfl, rfl⟩), ?_, hgraph, ?_⟩
  · intro n
    change Fin.lastCases (motive := fun _ : Fin (N + 2) => ℝ) x
      (fun i : Fin (N + 1) => B.cuts i.castSucc) n.castSucc = B.cuts n.castSucc
    exact Fin.lastCases_castSucc n
  · intro n
    refine ⟨?_, ?_⟩
    · change (γ n).U 0 = Fin.lastCases x (fun i => B.cuts i.castSucc) n.castSucc
      rw [Fin.lastCases_castSucc]
      exact (hends n).1
    · change (γ n).U (T n) =
        Fin.lastCases (min (B.cool (Fin.last N)) x) (fun i => B.cool i.castSucc) n
      refine Fin.lastCases ?_ (fun j => ?_) n
      · simpa only [Fin.lastCases_last, min_eq_left hx.1] using (hends (Fin.last N)).2
      · simpa only [Fin.lastCases_castSucc] using (hends j.castSucc).2
  · exact cutoff_variation_on_last_connector h B T hT γ hends hgraph hx

end EmcsfAcExtension.Global.Closure
