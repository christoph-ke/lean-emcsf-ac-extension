module

public import EmcsfAcExtension.Global.Closure.FinalPrefix
import EmcsfAcExtension.Global.Observation.CylinderClock
import Mathlib.Tactic

/-! # Cylinder families under cylinder and connector appends

Preserve the physical coordinate functions while their finite radius and
duration labels are transported to the appended boundary record.
Source: `charged_SF_new_version.tex:L3899–L3917`.
-/

public section

open Set

namespace EmcsfAcExtension.Global.Closure

/-- [internal]
Append one actual positive-duration cylinder to a finite clock family.
The old physical coordinate functions and all old durations are preserved;
the last functions are those of the supplied capped cylinder. The graph and
finite-record equalities are precisely those of `capped_boundary_append`.
Constants: none. -/
theorem append_clock_family {ui e a c d v₀ ρ R t : ℝ} {S : Fields}
    (h : OriginalData ui e S) {vb vb' : ℝ → ℝ} {N : ℕ}
    (B : FiniteBoundary S ui a c v₀ ρ vb N)
    (B' : FiniteBoundary S ui a d v₀ ρ vb' (N + 1))
    (T : Fin N → ℝ) (hT : ∀ n, 0 < T n)
    (γ : ∀ n, ClockCylinder S (origDomain ui) (B.radii n) 0 (T n))
    (hends : ∀ n, (γ n).U 0 = B.cuts n.castSucc ∧ (γ n).U (T n) = B.cool n)
    (hgraph : ∀ n, ∀ s ∈ Icc 0 (T n), vb ((γ n).U s) = (γ n).V s)
    (hold : ∀ u ∈ Icc a c, vb' u = vb u)
    (hcuts : ∀ i : Fin (N + 1), B'.cuts i.castSucc = B.cuts i)
    (hstages : ∀ i : Fin N, B'.cool i.castSucc = B.cool i ∧ B'.radii i.castSucc = B.radii i)
    (ht : 0 < t) (γlast : ClockCylinder S (origDomain ui) R 0 t)
    (hstart : γlast.U 0 = c) (hcool : B'.cool (Fin.last N) = γlast.U t)
    (hradius : B'.radii (Fin.last N) = R)
    (hlastgraph : ∀ s ∈ Icc 0 t, vb' (γlast.U s) = γlast.V s) :
    ∃ T' : Fin (N + 1) → ℝ,
    ∃ γ' : ∀ n, ClockCylinder S (origDomain ui) (B'.radii n) 0 (T' n),
      (∀ n, 0 < T' n) ∧
      (∀ n, (γ' n).U 0 = B'.cuts n.castSucc ∧ (γ' n).U (T' n) = B'.cool n) ∧
      (∀ n, ∀ s ∈ Icc 0 (T' n), vb' ((γ' n).U s) = (γ' n).V s) ∧
      (∀ i : Fin N, T' i.castSucc = T i ∧
        (γ' i.castSucc).U = (γ i).U ∧ (γ' i.castSucc).V = (γ i).V) ∧
      T' (Fin.last N) = t ∧ (γ' (Fin.last N)).U = γlast.U ∧
        (γ' (Fin.last N)).V = γlast.V := by
  let T' : Fin (N + 1) → ℝ := Fin.lastCases t T
  let γ' : ∀ n, ClockCylinder S (origDomain ui) (B'.radii n) 0 (T' n) := by
    intro n
    refine Fin.lastCases ?_ (fun i => ?_) n
    · exact castClockCylinder γlast _ _ hradius (Fin.lastCases_last)
    · exact castClockCylinder (γ i) _ _ (hstages i).2 (Fin.lastCases_castSucc _)
  have hprev (i : Fin N) : T' i.castSucc = T i ∧
      (γ' i.castSucc).U = (γ i).U ∧ (γ' i.castSucc).V = (γ i).V := by
    refine ⟨Fin.lastCases_castSucc _, ?_, ?_⟩ <;>
      simp only [γ', Fin.lastCases_castSucc, castClockCylinder]
  have hlast : T' (Fin.last N) = t ∧ (γ' (Fin.last N)).U = γlast.U ∧
      (γ' (Fin.last N)).V = γlast.V := by
    refine ⟨Fin.lastCases_last, ?_, ?_⟩ <;>
      simp only [γ', Fin.lastCases_last, castClockCylinder]
  have hcurve (i : Fin N) (s : ℝ) (hs : s ∈ Icc 0 (T i)) : (γ i).U s ∈ Icc a c := by
    have hm := ((γ i).strictMonoOn_U h.solution).monotoneOn
    have hl := hm ⟨le_rfl, (hT i).le⟩ hs hs.1
    have hr := hm hs ⟨(hT i).le, le_rfl⟩ hs.2
    rw [(hends i).1] at hl
    rw [(hends i).2] at hr
    exact ⟨(B.first.ge.trans (B.ordered (Fin.zero_le _))).trans hl,
      hr.trans ((B.split i).2.trans ((B.ordered (Fin.le_last _)).trans B.last.le))⟩
  refine ⟨T', γ', ?_, ?_, ?_, hprev, hlast⟩
  · intro n
    refine Fin.lastCases ?_ (fun i => ?_) n
    · simpa only [hlast.1] using ht
    · simpa only [(hprev i).1] using hT i
  · intro n
    refine Fin.lastCases ?_ (fun i => ?_) n
    · rw [hlast.2.1, hlast.1, hcuts, B.last, hcool]
      exact ⟨hstart, rfl⟩
    · rw [(hprev i).2.1, (hprev i).1, hcuts, (hstages i).1]
      exact hends i
  · intro n
    refine Fin.lastCases ?_ (fun i => ?_) n
    · rw [hlast.2.1, hlast.2.2, hlast.1]
      exact hlastgraph
    · rw [(hprev i).2.1, (hprev i).2.2, (hprev i).1]
      intro s hs
      rw [hold _ (hcurve i s hs)]
      exact hgraph i s hs

/-- [internal]
Extend only a connector, keeping every existing cylinder's clock duration
and physical coordinate functions. The equalities are the exact output of
`capped_last_connector`. Constants: none. -/
theorem connector_clock_family {ui e a c d v₀ ρ : ℝ} {S : Fields}
    (h : OriginalData ui e S) {vb vb' : ℝ → ℝ} {N : ℕ}
    (B : FiniteBoundary S ui a c v₀ ρ vb N)
    (B' : FiniteBoundary S ui a d v₀ ρ vb' N)
    (T : Fin N → ℝ) (hT : ∀ n, 0 < T n)
    (γ : ∀ n, ClockCylinder S (origDomain ui) (B.radii n) 0 (T n))
    (hends : ∀ n, (γ n).U 0 = B.cuts n.castSucc ∧ (γ n).U (T n) = B.cool n)
    (hgraph : ∀ n, ∀ s ∈ Icc 0 (T n), vb ((γ n).U s) = (γ n).V s)
    (hold : ∀ u ∈ Icc a c, vb' u = vb u)
    (hcuts : ∀ n : Fin N, B'.cuts n.castSucc = B.cuts n.castSucc)
    (hstages : ∀ n, B'.cool n = B.cool n ∧ B'.radii n = B.radii n) :
    ∃ γ' : ∀ n, ClockCylinder S (origDomain ui) (B'.radii n) 0 (T n),
      (∀ n, (γ' n).U = (γ n).U ∧ (γ' n).V = (γ n).V) ∧
      (∀ n, (γ' n).U 0 = B'.cuts n.castSucc ∧ (γ' n).U (T n) = B'.cool n) ∧
      (∀ n, ∀ s ∈ Icc 0 (T n), vb' ((γ' n).U s) = (γ' n).V s) := by
  let γ' : ∀ n, ClockCylinder S (origDomain ui) (B'.radii n) 0 (T n) :=
    fun n => castClockCylinder (γ n) _ _ (hstages n).2 rfl
  refine ⟨γ', (fun _ => ⟨rfl, rfl⟩), ?_, ?_⟩
  · intro n
    change (γ n).U 0 = B'.cuts n.castSucc ∧ (γ n).U (T n) = B'.cool n
    rw [hcuts, (hstages n).1]
    exact hends n
  · intro n s hs
    have hm := ((γ n).strictMonoOn_U h.solution).monotoneOn
    have hl := hm ⟨le_rfl, (hT n).le⟩ hs hs.1
    have hr := hm hs ⟨(hT n).le, le_rfl⟩ hs.2
    rw [(hends n).1] at hl
    rw [(hends n).2] at hr
    have hu : (γ n).U s ∈ Icc a c :=
      ⟨(B.first.ge.trans (B.ordered (Fin.zero_le _))).trans hl,
        hr.trans ((B.split n).2.trans ((B.ordered (Fin.le_last _)).trans B.last.le))⟩
    change vb' ((γ n).U s) = (γ n).V s
    rw [hold _ hu]
    exact hgraph n s hs

end EmcsfAcExtension.Global.Closure
