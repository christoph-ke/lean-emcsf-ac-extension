module

public import EmcsfAcExtension.Global.Closure.FinalSelection
public import EmcsfAcExtension.Global.Assembly.Inputs
import Mathlib.Tactic

/-! # Transferring completed histories to the common closure data

Use the common actual variation sequence for every prescribed energy and
budget. Transfer the finite records and full connector-inclusive budgets
to one graph. The radial reconstruction is applied at every earlier cut
using prefix `n+1`, as required by the assembly audit.
Source: `charged_SF_new_version.tex:L3919–L3932`, `charged_SF_new_version.tex:L3955–L4050`.
-/

public section

open Set

namespace EmcsfAcExtension.Global.Closure

/-- [internal]
Package compatible completed histories into the exact common-boundary
closure data. The finite estimates are the joint quantitative/budget output
of `actual_cutoff_callback_of_small_entry`; all graph transfer, common
energies, uniform sum cap, amplitudes and radial inequalities are proved
here. This conditional helper closes no graph node. The fixed coefficients
and logarithmic majorant precede the compatible history and stage index. -/
theorem closure_entry_of_coherent_prefixes {S : Fields}
    {ui e a v₀ ρ b₀ H χ C₁ εentry R₀ δ c Λ F εweak εrun εabs Cbudget Csum A D M ζ : ℝ}
    (h : OriginalData ui e S) (hbox : ExteriorBox δ c Λ F εweak ρ)
    (hρ : 0 ≤ ρ ∧ ρ < 1) (he : 0 ≤ εentry) (hA : 0 ≤ A) (hCsum : 0 ≤ Csum)
    (hrun : 0 ≤ εrun ∧ εrun ≤ εabs) (hR : S.r a 0 = R₀)
    (hM : Interaction.scalarBackground ui R₀ c F εabs S ≤ M)
    (herror : (initialInteraction S a v₀).toReal + εentry + ζ ≤
      D + εentry + e ^ 2 * M ^ 2 * R₀ ^ 2)
    (P : ∀ N, FinalPrefix S ui e a v₀ ρ b₀ H χ C₁ εentry R₀ δ c Λ F εweak εrun N)
    (hgraph : ∀ L N, L ≤ N → EqOn (P N).graph (P L).graph (Icc a (P L).endpoint))
    (hcuts : ∀ N (i : Fin (N + 1)), (P N).boundary.cuts i = (P i).endpoint)
    (hvar : ∀ L N, L ≤ N → ∀ k < L, (P N).variation k = (P L).variation k)
    (hest : ∀ N, 0 < N →
      let J := (interactionNorm e S (exteriorDomain ui a (P N).endpoint (P N).graph) a v₀).toReal
      let V := ∑ n, (curveCovVar e S S.a ((P N).cylinders n).U ((P N).cylinders n).V
        0 ((P N).duration n)).toReal
      J + V ≤ A * ((initialInteraction S a v₀).toReal + εentry + ζ) ∧
      BoundaryBudgets S ui a (P N).endpoint v₀ ρ (P N).graph N (P N).boundary
        (fun n => stageBudget Cbudget χ C₁ εentry (P N).variation n) ∧
      (∑ n : Fin N, stageBudget Cbudget χ C₁ εentry (P N).variation n) ≤
        Csum * (εentry + V ^ 2)) :
    ∃ K : ℝ, ∃ U : ℕ → ℝ, ∃ vb : ℝ → ℝ,
    ∃ B : ∀ N, FiniteBoundary S ui a (U N) v₀ ρ vb N, ∃ E J : ℕ → ℝ,
      (0 ≤ ρ ∧ ρ < 1) ∧ Monotone U ∧ (∀ N i, (B N).cuts i = U i) ∧
      (∀ n, R₀ / 2 ≤ S.r (U n) 0) ∧
      (∀ n, S.r (U n) (vb (U n)) = stageRadius ρ b₀ n) ∧
      (∀ N, BoundaryBudgets S ui a (U N) v₀ ρ vb N (B N) (fun i => E i)) ∧
      (∀ N, ∑ n ∈ Finset.range N, E n ≤ K) ∧
      (∀ n, ‖S.phi (U n) (vb (U n))‖ ≤ M) ∧
      (∀ n, J n ≤ A * (D + εentry + e ^ 2 * M ^ 2 * R₀ ^ 2)) ∧
      ∀ n, (1 - F ^ 2) * (eVariationOn (S.a (U n)) (Icc (vb (U n)) 0)).toReal ≤
        c⁻¹ * J n + F ^ 2 * ‖S.theta (U n) (vb (U n)) / (S.lam (U n) (vb (U n)) : ℂ)‖ := by
  let U := fun N => (P N).endpoint
  let σ := fun n => (P (n + 1)).variation n
  let E := stageBudget Cbudget χ C₁ εentry σ
  let J := fun n =>
    (interactionNorm e S (exteriorDomain ui a (U (n + 1)) (P (n + 1)).graph) a v₀).toReal
  obtain ⟨_, _, hEeq⟩ := common_variations_of_coherent_prefixes P hvar
  have hE (N : ℕ) : BoundaryBudgets S ui a (U N) v₀ ρ (P N).graph N
      (P N).boundary (fun i => E i) := by
    by_cases hN : 0 < N
    · have hb := (hest N hN).2.1
      have heq : (fun i : Fin N => stageBudget Cbudget χ C₁ εentry (P N).variation i) =
          (fun i : Fin N => E i) := by
        funext i
        exact hEeq Cbudget N i i.isLt
      rw [heq] at hb
      exact hb
    · have hzero : N = 0 := by omega
      subst N
      intro i
      exact Fin.elim0 i
  obtain ⟨vb, B, hcommon, hBcuts, hBud⟩ := common_finite_boundaries_of_coherent_prefixes U
    (fun N => (P N).graph) (fun N => (P N).boundary) E hgraph hE
  have hac (N : ℕ) : a ≤ U N := by
    simpa only [(P N).boundary.first, (P N).boundary.last] using
      (P N).boundary.ordered (Fin.zero_le (Fin.last N))
  have hU : Monotone U := by
    apply monotone_nat_of_le_succ
    intro n
    have hh := (P (n + 1)).boundary.ordered (Fin.castSucc_le_succ (Fin.last n))
    simpa only [hcuts, Fin.val_castSucc, Fin.val_succ, Fin.val_last] using hh
  have hV (N : ℕ) : 0 ≤ ∑ n,
      (curveCovVar e S S.a ((P N).cylinders n).U ((P N).cylinders n).V
        0 ((P N).duration n)).toReal :=
    Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg)
  have hJrun (N : ℕ) :
      (interactionNorm e S (exteriorDomain ui a (U N) (P N).graph) a v₀).toReal ≤ εrun := by
    have hb := (P N).stops.2.2.2
    linarith only [hb, hV N]
  have hVrun (N : ℕ) : (∑ n,
      (curveCovVar e S S.a ((P N).cylinders n).U ((P N).cylinders n).V
        0 ((P N).duration n)).toReal) ≤
      εrun := by
    have hb := (P N).stops.2.2.2
    have hJ : 0 ≤ (interactionNorm e S (exteriorDomain ui a (U N) (P N).graph) a v₀).toReal :=
      ENNReal.toReal_nonneg
    linarith only [hb, hJ]
  have hprofile (N : ℕ) := stopped_radial_variation h (P N).boundary hbox (P N).stops.1 hR
    (fun u hu => ((P N).stops.2.2.1 u hu).le) ((hJrun N).trans hrun.2)
  let K := Csum * (εentry + εrun ^ 2)
  refine ⟨K, U, vb, B, E, J, hρ, hU, ?_, ?_, ?_, hBud, ?_, ?_, ?_, ?_⟩
  · intro N i
    exact (hBcuts N i).trans (hcuts N i)
  · intro n
    exact ((P n).stops.2.2.1 (U n) ⟨hac n, le_rfl⟩).le
  · intro n
    rw [hcommon n ⟨hac n, le_rfl⟩]
    exact (P n).endpoint_radius
  · intro N
    by_cases hN : 0 < N
    · rw [Finset.sum_range]
      have heq : (∑ i : Fin N, E i) =
          ∑ i : Fin N, stageBudget Cbudget χ C₁ εentry (P N).variation i := by
        apply Finset.sum_congr rfl
        intro i _
        exact (hEeq Cbudget N i i.isLt).symm
      rw [heq]
      exact (hest N hN).2.2.trans (mul_le_mul_of_nonneg_left
        (add_le_add le_rfl ((sq_le_sq₀ (hV N) hrun.1).mpr (hVrun N))) hCsum)
    · have hzero : N = 0 := by omega
      subst N
      simp only [Finset.range_zero, Finset.sum_empty]
      dsimp only [K]
      positivity
  · intro n
    have hu : U n ∈ Icc a (U (n + 1)) := ⟨hac n, hU (Nat.le_succ n)⟩
    rw [hcommon (n + 1) hu]
    exact ((hprofile (n + 1) _ hu).2.2 _ ⟨le_rfl,
      ((P (n + 1)).boundary.mem _ hu).2.2.2⟩).trans hM
  · intro n
    have hb := (hest (n + 1) (Nat.zero_lt_succ n)).1
    have hh : J n ≤ A * ((initialInteraction S a v₀).toReal + εentry + ζ) := by
      linarith only [hb, hV (n + 1)]
    exact hh.trans (mul_le_mul_of_nonneg_left herror hA)
  · intro n
    have hu : U n ∈ Icc a (U (n + 1)) := ⟨hac n, hU (Nat.le_succ n)⟩
    rw [hcommon (n + 1) hu]
    have hb := (hprofile (n + 1) _ hu).2.1
    change (1 - F ^ 2) * _ ≤ c⁻¹ *
      (interactionNorm e S (exteriorDomain ui a (U (n + 1)) (P (n + 1)).graph) a v₀).toReal + _
    linarith only [hb]

end EmcsfAcExtension.Global.Closure
