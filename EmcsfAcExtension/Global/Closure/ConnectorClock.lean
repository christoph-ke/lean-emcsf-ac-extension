module

public import EmcsfAcExtension.Global.Closure.Windows
public import EmcsfAcExtension.Global.Closure.Clock
import Mathlib.Tactic

/-! # Clock and accumulated variation on a constant-label connector

The literal clipped variation stops accumulating after the last cylinder.
Extending that cylinder's connector adds exactly its radial loss to the
mixed boundary clock. Source: `charged_SF_new_version.tex:L3919–L3929`,
`charged_SF_new_version.tex:L4074–L4083`.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Global.Closure

/-- [internal]
Throughout the last incoming connector the literal clipped cylinder
variation equals the sum of the completed cylinder variations. This is the
connector counterpart of `cutoff_variation_on_last_cylinder` and uses
`monotoneOn_cylinderClock` on the actual whole finite path. Durations may
be zero, as allowed by finite cutoff continuity. Constants: none. -/
theorem cutoff_variation_on_last_connector {ui e a b v₀ ρ : ℝ} {S : Fields}
    (h : OriginalData ui e S) {vb : ℝ → ℝ} {N : ℕ}
    (B : FiniteBoundary S ui a b v₀ ρ vb (N + 1))
    (T : Fin (N + 1) → ℝ) (hT : ∀ n, 0 ≤ T n)
    (γ : ∀ n, ClockCylinder S (origDomain ui) (B.radii n) 0 (T n))
    (hends : ∀ n, (γ n).U 0 = B.cuts n.castSucc ∧ (γ n).U (T n) = B.cool n)
    (hgraph : ∀ n, ∀ τ ∈ Icc 0 (T n), vb ((γ n).U τ) = (γ n).V τ)
    {x : ℝ} (hx : x ∈ Icc (B.cool (Fin.last N)) b) :
    (∑ n, (curveCovVar e S S.a (γ n).U (γ n).V 0
      (max 0 (min (T n) (cylinderClock S vb (B.cuts n.castSucc) x)))).toReal) =
      ∑ n, (curveCovVar e S S.a (γ n).U (γ n).V 0 (T n)).toReal := by
  have hfirst (i : Fin (N + 2)) : a ≤ B.cuts i :=
    B.first.ge.trans (B.ordered (Fin.zero_le i))
  have hlast (i : Fin (N + 2)) : B.cuts i ≤ b :=
    (B.ordered (Fin.le_last i)).trans B.last.le
  have hcool (n : Fin (N + 1)) : B.cool n ∈ Icc a b :=
    ⟨(hfirst _).trans (B.split n).1, (B.split n).2.trans (hlast _)⟩
  have hx' : x ∈ Icc a b := ⟨(hcool _).1.trans hx.1, hx.2⟩
  have hafter (n : Fin (N + 1)) : B.cool n ≤ x := by
    refine Fin.lastCases hx.1 (fun j => ?_) n
    have hind : j.castSucc.succ ≤ (Fin.last N).castSucc := by
      apply Fin.le_iff_val_le_val.mpr
      simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_last]
      omega
    exact (B.split _).2.trans ((B.ordered hind).trans ((B.split _).1.trans hx.1))
  apply Finset.sum_congr rfl
  intro n _
  have hseg : Icc ((γ n).U 0) ((γ n).U (T n)) ⊆ Icc a b := by
    rw [(hends n).1, (hends n).2]
    exact Icc_subset_Icc (hfirst _) (hcool n).2
  have hclock := cylinder_clock_at_parameter h (hT n) (γ n) vb
    (B.cont.mono hseg) (fun u hu => B.mem u (hseg hu)) (hgraph n)
    (right_mem_Icc.mpr (hT n))
  rw [(hends n).1, (hends n).2] at hclock
  have hle : T n ≤ cylinderClock S vb (B.cuts n.castSucc) x := by
    rw [← hclock]
    exact monotoneOn_cylinderClock h B ⟨hfirst _, hlast _⟩ (hcool n) hx' (hafter n)
  rw [min_eq_left hle, max_eq_right (hT n)]

end EmcsfAcExtension.Global.Closure
