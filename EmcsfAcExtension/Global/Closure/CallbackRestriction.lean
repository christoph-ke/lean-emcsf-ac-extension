module

public import EmcsfAcExtension.Global.Closure.CallbackPaths
import Mathlib.Tactic

/-! # Realizing every noninitial finite cutoff

Locate the visited stage, discard future cylinders, and restrict the last
available cylinder or connector. All functions in the stopping predicate
remain the literal incoming norm and clipped variation.
Source: `charged_SF_new_version.tex:L4104–L4106`.
-/

public section

open Set

namespace EmcsfAcExtension.Global.Closure

/-- [internal]
Every cutoff strictly after entry has a nonempty finite realization on the
same graph. Earlier clocks and all starting cuts/radii are inherited; only
the last clock may be shortened. Its full variation sum equals the original
literal clipped sum. Constants: none. This is a geometric construction,
with no weak stops, energy estimates or boundary budgets as inputs. -/
theorem finite_cutoff_realization {ui e a b v₀ ρ : ℝ} {S : Fields}
    (h : OriginalData ui e S) {vb : ℝ → ℝ} {N : ℕ}
    (B : FiniteBoundary S ui a b v₀ ρ vb N) (T : Fin N → ℝ) (hT : ∀ n, 0 < T n)
    (γ : ∀ n, ClockCylinder S (origDomain ui) (B.radii n) 0 (T n))
    (hends : ∀ n, (γ n).U 0 = B.cuts n.castSucc ∧ (γ n).U (T n) = B.cool n)
    (hgraph : ∀ n, ∀ s ∈ Icc 0 (T n), vb ((γ n).U s) = (γ n).V s)
    {x : ℝ} (hx : x ∈ Ioc a b) :
    ∃ M : ℕ, ∃ hMN : M ≤ N, 0 < M ∧
    ∃ B' : FiniteBoundary S ui a x v₀ ρ vb M,
    ∃ T' : Fin M → ℝ,
    ∃ γ' : ∀ n, ClockCylinder S (origDomain ui) (B'.radii n) 0 (T' n),
      (∀ n : Fin M, B'.cuts n.castSucc = B.cuts (n.castLE hMN).castSucc) ∧
      (∀ n, B'.radii n = B.radii (n.castLE hMN)) ∧
      (∀ n, 0 < T' n ∧ T' n ≤ T (n.castLE hMN)) ∧
      (∀ n, n.val + 1 < M → T' n = T (n.castLE hMN)) ∧
      (∀ n, (γ' n).U = (γ (n.castLE hMN)).U ∧
        (γ' n).V = (γ (n.castLE hMN)).V) ∧
      (∀ n, (γ' n).U 0 = B'.cuts n.castSucc ∧ (γ' n).U (T' n) = B'.cool n) ∧
      (∀ n, ∀ s ∈ Icc 0 (T' n), vb ((γ' n).U s) = (γ' n).V s) ∧
      (∑ n, (curveCovVar e S S.a (γ n).U (γ n).V 0
        (max 0 (min (T n) (cylinderClock S vb (B.cuts n.castSucc) x)))).toReal) =
        ∑ n, (curveCovVar e S S.a (γ' n).U (γ' n).V 0 (T' n)).toReal := by
  obtain ⟨n, hnx, hxn⟩ := exists_stage_at_cutoff B hx
  have hMN : n.val + 1 ≤ N := n.isLt
  let BP := takeBoundary B (n.val + 1) hMN
  let TP := fun i : Fin (n.val + 1) => T (i.castLE hMN)
  let γP : ∀ i, ClockCylinder S (origDomain ui) (BP.radii i) 0 (TP i) :=
    fun i => γ (i.castLE hMN)
  have hTP (i) : 0 < TP i := hT _
  have hEP (i) : (γP i).U 0 = BP.cuts i.castSucc ∧
      (γP i).U (TP i) = BP.cool i := hends _
  have hGP (i) (s) (hs : s ∈ Icc 0 (TP i)) : vb ((γP i).U s) = (γP i).V s :=
    hgraph _ s hs
  have htake := cutoff_variation_take h B T γ (n.val + 1) hMN ⟨hx.1.le, hx.2⟩ hxn
  by_cases hxc : x ≤ BP.cool (Fin.last n.val)
  · have hinterval : x ∈ Icc ((γP (Fin.last n.val)).U 0)
        ((γP (Fin.last n.val)).U (TP (Fin.last n.val))) := by
      rw [(hEP _).1, (hEP _).2]
      exact ⟨hnx.le, hxc⟩
    obtain ⟨τ, hτ, hxτ⟩ := intermediate_value_Icc (hTP _).le
      (γP (Fin.last n.val)).c1_U.continuousOn hinterval
    have hτpos : 0 < τ := by
      by_contra hnτ
      have heq : τ = 0 := le_antisymm (le_of_not_gt hnτ) hτ.1
      rw [heq, (hEP _).1] at hxτ
      exact (ne_of_lt hnx) hxτ
    subst x
    obtain ⟨B', T', γ', hcuts, hradii, hshort, hprev, hcurves, hends', hgraph', hvar⟩ :=
      last_cylinder_cutoff_path h BP TP hTP γP hEP hGP ⟨hτpos, hτ.2⟩
    refine ⟨n.val + 1, hMN, by omega, B', T', γ', hcuts, hradii, hshort, ?_,
      hcurves, hends', hgraph', htake.trans hvar⟩
    intro i hi
    have hieq : i = (⟨i.val, by omega⟩ : Fin n.val).castSucc := rfl
    rw [hieq]
    exact hprev _
  · obtain ⟨B', γ', hcuts, hradii, hcurves, hends', hgraph', hvar⟩ :=
      last_connector_cutoff_path h BP TP (fun i => (hTP i).le) γP hEP hGP
        ⟨(lt_of_not_ge hxc).le, hxn⟩
    exact ⟨n.val + 1, hMN, by omega, B', TP, γ', hcuts, hradii,
      (fun i => ⟨hTP i, le_rfl⟩), (fun _ _ => rfl),
      hcurves, hends', hgraph', htake.trans hvar⟩

end EmcsfAcExtension.Global.Closure
