module

public import EmcsfAcExtension.Global.Closure.FinalPrefix
import Mathlib.Tactic

/-! # Coherent selection of completed finite histories

Dependent choice selects successive actual histories. Induction on the
larger cutoff then gives compatibility of every pair of prefixes, one
global sequence of cuts, and one global sequence of actual variations.
Source: `charged_SF_new_version.tex:L4106–L4115`.
-/

public section

open Set

namespace EmcsfAcExtension.Global.Closure

/-- [internal]
Choose compatible completed histories from the proved one-stage extension
relation. The input is explicit and is discharged by
`final_prefix_extension_of_stopped_paths`; no graph node is claimed here.
Every pair of histories agrees on the smaller graph, cuts and variations.
Constants: none are selected. -/
theorem coherent_final_prefixes_of_extension {S : Fields}
    {ui e a v₀ ρ b₀ H χ C₁ εentry R₀ δ c Λ F εweak εrun : ℝ}
    (P₀ : FinalPrefix S ui e a v₀ ρ b₀ H χ C₁ εentry R₀ δ c Λ F εweak εrun 0)
    (hstep : ∀ N,
      ∀ P : FinalPrefix S ui e a v₀ ρ b₀ H χ C₁ εentry R₀ δ c Λ F εweak εrun N,
      ∃ Q : FinalPrefix S ui e a v₀ ρ b₀ H χ C₁ εentry R₀ δ c Λ F εweak εrun (N + 1),
        P.endpoint < Q.endpoint ∧ EqOn Q.graph P.graph (Icc a P.endpoint) ∧
        (∀ i : Fin (N + 1), Q.boundary.cuts i.castSucc = P.boundary.cuts i) ∧
        ∀ k < N, Q.variation k = P.variation k) :
    ∃ P : ∀ N, FinalPrefix S ui e a v₀ ρ b₀ H χ C₁ εentry R₀ δ c Λ F εweak εrun N,
      P 0 = P₀ ∧ Monotone (fun N => (P N).endpoint) ∧
      (∀ M N, M ≤ N → EqOn (P N).graph (P M).graph (Icc a (P M).endpoint)) ∧
      (∀ N (i : Fin (N + 1)), (P N).boundary.cuts i = (P i).endpoint) ∧
      ∀ M N, M ≤ N → ∀ k < M, (P N).variation k = (P M).variation k := by
  let α := fun N => FinalPrefix S ui e a v₀ ρ b₀ H χ C₁ εentry R₀ δ c Λ F εweak εrun N
  let R := fun N (P : α N) (Q : α (N + 1)) =>
    P.endpoint < Q.endpoint ∧ EqOn Q.graph P.graph (Icc a P.endpoint) ∧
      (∀ i : Fin (N + 1), Q.boundary.cuts i.castSucc = P.boundary.cuts i) ∧
      ∀ k < N, Q.variation k = P.variation k
  obtain ⟨P, hP₀, hP⟩ := coherent_sequence_of_extension R P₀ hstep
  have hU : Monotone (fun N => (P N).endpoint) :=
    monotone_nat_of_le_succ (fun N => (hP N).1.le)
  have hgraph : ∀ M N, M ≤ N → EqOn (P N).graph (P M).graph (Icc a (P M).endpoint) := by
    intro M N hMN
    induction N, hMN using Nat.le_induction with
    | base => exact fun _ _ => rfl
    | succ N hMN ih =>
      intro u hu
      exact ((hP N).2.1 ⟨hu.1, hu.2.trans (hU hMN)⟩).trans (ih hu)
  have hcuts : ∀ M N (hMN : M ≤ N) (i : Fin (M + 1)),
      (P N).boundary.cuts (i.castLE (Nat.add_le_add_right hMN 1)) =
        (P M).boundary.cuts i := by
    intro M N hMN i
    induction N, hMN using Nat.le_induction with
    | base => rfl
    | succ N hMN ih =>
      let j := i.castLE (Nat.add_le_add_right hMN 1)
      change (P (N + 1)).boundary.cuts j.castSucc = (P M).boundary.cuts i
      rw [(hP N).2.2.1 j]
      exact ih
  have hvar : ∀ M N, M ≤ N → ∀ k < M, (P N).variation k = (P M).variation k := by
    intro M N hMN k hk
    induction N, hMN using Nat.le_induction with
    | base => rfl
    | succ N hMN ih => exact ((hP N).2.2.2 k (hk.trans_le hMN)).trans ih
  refine ⟨P, hP₀, hU, hgraph, ?_, hvar⟩
  intro N i
  have hiN : i.val ≤ N := by have hi := i.isLt; omega
  have hc := hcuts i N hiN (Fin.last i.val)
  have hieq : (Fin.last i.val).castLE (Nat.add_le_add_right hiN 1) = i := Fin.ext rfl
  rw [hieq, (P i).boundary.last] at hc
  exact hc

/-- [internal]
The single actual variation sequence selected from completed prefix `n+1`
agrees with every longer available prefix. Its stage budgets and energy
envelopes therefore agree on every visited index. Constants: none. -/
theorem common_variations_of_coherent_prefixes {S : Fields}
    {ui e a v₀ ρ b₀ H χ C₁ εentry R₀ δ c Λ F εweak εrun : ℝ}
    (P : ∀ N, FinalPrefix S ui e a v₀ ρ b₀ H χ C₁ εentry R₀ δ c Λ F εweak εrun N)
    (hvar : ∀ M N, M ≤ N → ∀ k < M, (P N).variation k = (P M).variation k) :
    let σ := fun n => (P (n + 1)).variation n
    (∀ N k, k < N → (P N).variation k = σ k) ∧
    (∀ N k, k ≤ N → energyEnvelope χ C₁ εentry (P N).variation k =
      energyEnvelope χ C₁ εentry σ k) ∧
    ∀ Cbudget N k, k < N → stageBudget Cbudget χ C₁ εentry (P N).variation k =
      stageBudget Cbudget χ C₁ εentry σ k := by
  dsimp only
  let σ := fun n => (P (n + 1)).variation n
  have heq (N k : ℕ) (hk : k < N) : (P N).variation k = σ k :=
    hvar (k + 1) N hk k (Nat.lt_succ_self k)
  have henv (N k : ℕ) (hk : k ≤ N) :
      energyEnvelope χ C₁ εentry (P N).variation k = energyEnvelope χ C₁ εentry σ k := by
    apply energyEnvelope_congr_before
    intro j hj
    exact heq N j (hj.trans_le hk)
  refine ⟨heq, henv, ?_⟩
  intro Cbudget N k hk
  unfold stageBudget
  rw [henv N k hk.le, heq N k hk]

end EmcsfAcExtension.Global.Closure
