/- Copyright (c) 2026. All rights reserved. -/

module

public import EmcsfAcExtension.Infra.ODE.LocalFlow
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Maximal ODE solutions and compact-subset continuation

internal project record infrastructure for internal project record, `eq:co-static` and the strict
static
barriers. Maximal solutions are constructed only after local existence and
uniqueness, by joining the compatible local solutions.
-/

public section

open Set Metric Filter
open scoped Topology NNReal

namespace EmcsfAcExtension.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem patch_solutions {f : ℝ → E → E} {U : Set E}
    {D D' : Set ℝ} {y z : ℝ → E} (hD : IsOpen D) (hD' : IsOpen D')
    (hy : ∀ t ∈ D, HasDerivAt y (f t (y t)) t)
    (hz : ∀ t ∈ D', HasDerivAt z (f t (z t)) t)
    (hyU : MapsTo y D U) (hzU : MapsTo z D' U) (heq : EqOn y z (D ∩ D')) :
    ∃ w : ℝ → E, EqOn w y D ∧ EqOn w z D' ∧
      (∀ t ∈ D ∪ D', HasDerivAt w (f t (w t)) t) ∧ MapsTo w (D ∪ D') U := by
  classical
  let w := D.piecewise y z
  have hwy : EqOn w y D := fun _ ht => piecewise_eq_of_mem D y z ht
  have hwz : EqOn w z D' := by
    intro t ht
    by_cases htD : t ∈ D
    · exact (hwy htD).trans (heq ⟨htD, ht⟩)
    · exact piecewise_eq_of_notMem D y z htD
  refine ⟨w, hwy, hwz, ?_, ?_⟩
  · intro t ht
    rcases ht with ht | ht
    · rw [hwy ht]
      exact (hy t ht).congr_of_eventuallyEq
        (mem_of_superset (hD.mem_nhds ht) hwy)
    · rw [hwz ht]
      exact (hz t ht).congr_of_eventuallyEq
        (mem_of_superset (hD'.mem_nhds ht) hwz)
  · intro t ht
    rcases ht with ht | ht
    · rw [hwy ht]; exact hyU ht
    · rw [hwz ht]; exact hzU ht

/-- A maximal solution through each point of an open state domain. Every other
solution through the same initial point on a connected open time domain is a
restriction of this solution. Local state Lipschitz constants need not be uniform
on the entire domain. This is an existence theorem, with no chosen flow definition. -/
theorem exists_maximal_solution [FiniteDimensional ℝ E]
    {f : ℝ → E → E} {U : Set E} (hU : IsOpen U)
    (hcont : ContinuousOn (Function.uncurry f) (univ ×ˢ U))
    (hlocal : ∀ t : ℝ, ∀ x ∈ U, ∃ (r δ : ℝ) (K : ℝ≥0), 0 < r ∧ 0 < δ ∧
      ∀ s ∈ Icc (t - δ) (t + δ), LipschitzOnWith K (f s) (closedBall x r))
    (t₀ : ℝ) (x₀ : E) (hx₀ : x₀ ∈ U) :
    ∃ (D : Set ℝ) (y : ℝ → E), IsOpen D ∧ OrdConnected D ∧ t₀ ∈ D ∧ y t₀ = x₀ ∧
      (∀ t ∈ D, HasDerivAt y (f t (y t)) t) ∧ MapsTo y D U ∧
      ∀ (D' : Set ℝ) (z : ℝ → E), IsOpen D' → OrdConnected D' → t₀ ∈ D' →
        z t₀ = x₀ → (∀ t ∈ D', HasDerivAt z (f t (z t)) t) → MapsTo z D' U →
        D' ⊆ D ∧ EqOn z y D' := by
  classical
  let I := {w : Set ℝ × (ℝ → E) // IsOpen w.1 ∧ OrdConnected w.1 ∧
    t₀ ∈ w.1 ∧ w.2 t₀ = x₀ ∧
    (∀ t ∈ w.1, HasDerivAt w.2 (f t (w.2 t)) t) ∧ MapsTo w.2 w.1 U}
  obtain ⟨ε, hε, z, hz₀, hz, hzU⟩ :=
    exists_local_solution hU hcont t₀ x₀ hx₀ (hlocal t₀)
  let i₀ : I := ⟨(Ioo (t₀ - ε) (t₀ + ε), z), isOpen_Ioo, ordConnected_Ioo,
    ⟨by linarith, by linarith⟩, hz₀, hz, hzU⟩
  let D : Set ℝ := ⋃ i : I, i.1.1
  have hD : IsOpen D := isOpen_iUnion fun i => i.2.1
  have ht₀ : t₀ ∈ D := mem_iUnion.mpr ⟨i₀, i₀.2.2.2.1⟩
  have hcD : OrdConnected D := (isPreconnected_iUnion
    ⟨t₀, mem_iInter.mpr fun i => i.2.2.2.1⟩
    (fun i => i.2.2.1.isPreconnected)).ordConnected
  have hlip (D' : Set ℝ) : ∀ t ∈ D', ∀ x ∈ U, ∃ (r δ : ℝ) (K : ℝ≥0),
      0 < r ∧ 0 < δ ∧ ∀ s ∈ Ioo (t - δ) (t + δ),
        LipschitzOnWith K (f s) (closedBall x r) := by
    intro t _ x hx
    obtain ⟨r, δ, K, hr, hδ, hK⟩ := hlocal t x hx
    exact ⟨r, δ, K, hr, hδ, fun s hs => hK s (Ioo_subset_Icc_self hs)⟩
  have hagree (i j : I) : EqOn i.1.2 j.1.2 (i.1.1 ∩ j.1.1) := by
    apply solution_eqOn_of_locally_lipschitz (i.2.1.inter j.2.1)
      (i.2.2.1.inter j.2.2.1).isPreconnected ⟨i.2.2.2.1, j.2.2.2.1⟩ (hlip _)
      (fun t ht => i.2.2.2.2.2.1 t ht.1)
      (fun t ht => j.2.2.2.2.2.1 t ht.2)
      (fun _ ht => i.2.2.2.2.2.2 ht.1)
      (fun _ ht => j.2.2.2.2.2.2 ht.2)
    exact i.2.2.2.2.1.trans j.2.2.2.2.1.symm
  have hex (t : D) : ∃ i : I, (t : ℝ) ∈ i.1.1 := mem_iUnion.mp t.2
  choose idx hidx using hex
  let y : ℝ → E := fun t => if ht : t ∈ D then (idx ⟨t, ht⟩).1.2 t else x₀
  have heq (i : I) : EqOn y i.1.2 i.1.1 := by
    intro t ht
    have htD : t ∈ D := mem_iUnion.mpr ⟨i, ht⟩
    change (if h : t ∈ D then (idx ⟨t, h⟩).1.2 t else x₀) = i.1.2 t
    rw [dite_eq_left htD]
    exact hagree (idx ⟨t, htD⟩) i ⟨hidx ⟨t, htD⟩, ht⟩
  refine ⟨D, y, hD, hcD, ht₀, (heq i₀ i₀.2.2.2.1).trans hz₀, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨i, hti⟩ := mem_iUnion.mp ht
    rw [heq i hti]
    exact (i.2.2.2.2.2.1 t hti).congr_of_eventuallyEq
      (mem_of_superset (i.2.1.mem_nhds hti) (heq i))
  · intro t ht
    obtain ⟨i, hti⟩ := mem_iUnion.mp ht
    rw [heq i hti]
    exact i.2.2.2.2.2.2 hti
  · intro D' z hD' hcD' ht₀' hz₀' hz' hzU'
    let i : I := ⟨(D', z), hD', hcD', ht₀', hz₀', hz', hzU'⟩
    exact ⟨fun _ ht => mem_iUnion.mpr ⟨i, ht⟩, (heq i).symm⟩

/-- A maximal solution reaches a finite target time when an a priori estimate
places every state before that time in a compact subset of its open state domain.
The maximality premise is discharged by `exists_maximal_solution`; the compact
bound is discharged by the comparison estimate in the parameter dependence theorem. -/
theorem Icc_subset_domain_of_maximal_of_mem_isCompact [FiniteDimensional ℝ E]
    {f : ℝ → E → E} {U C : Set E} {D : Set ℝ} {a b : ℝ} {y : ℝ → E}
    (hab : a ≤ b) (hU : IsOpen U) (hC : IsCompact C) (hCU : C ⊆ U)
    (hcont : ContinuousOn (Function.uncurry f) (univ ×ˢ U))
    (hlocal : ∀ t : ℝ, ∀ x ∈ U, ∃ (r δ : ℝ) (K : ℝ≥0), 0 < r ∧ 0 < δ ∧
      ∀ s ∈ Icc (t - δ) (t + δ), LipschitzOnWith K (f s) (closedBall x r))
    (hD : IsOpen D) (hcD : OrdConnected D) (ha : a ∈ D)
    (hy : ∀ t ∈ D, HasDerivAt y (f t (y t)) t) (hyU : MapsTo y D U)
    (hmax : ∀ (D' : Set ℝ) (z : ℝ → E), IsOpen D' → OrdConnected D' → a ∈ D' →
      z a = y a → (∀ t ∈ D', HasDerivAt z (f t (z t)) t) → MapsTo z D' U → D' ⊆ D)
    (hbound : ∀ t ∈ D ∩ Icc a b, y t ∈ C) : Icc a b ⊆ D := by
  let : PreconnectedSpace (Icc a b) := Subtype.preconnectedSpace ordConnected_Icc.isPreconnected
  have hopen : IsOpen {t : Icc a b | (t : ℝ) ∈ D} := hD.preimage continuous_subtype_val
  have hclosed : IsClosed {t : Icc a b | (t : ℝ) ∈ D} := by
    apply isClosed_of_closure_subset
    intro t ht
    obtain ⟨ε, hε, hsol⟩ := exists_uniform_local_solution_scalar hU hC hCU hcont t (hlocal t)
    obtain ⟨τ, hτ, hτdist⟩ := Metric.mem_closure_iff.mp ht (ε / 2) (half_pos hε)
    have hτabs : |(τ : ℝ) - (t : ℝ)| < ε / 2 := by
      simpa only [Subtype.dist_eq, Real.dist_eq, abs_sub_comm] using hτdist
    have hτt : (τ : ℝ) ∈ Icc ((t : ℝ) - ε) ((t : ℝ) + ε) := by
      constructor <;> linarith [(abs_lt.mp hτabs).1, (abs_lt.mp hτabs).2]
    obtain ⟨z, hz₀, hz, hzU⟩ := hsol τ hτt (y τ) (hbound τ ⟨hτ, τ.2⟩)
    have hz' : ∀ s ∈ Ioo ((τ : ℝ) - ε) ((τ : ℝ) + ε),
        HasDerivAt z (f s (z s)) s :=
      fun s hs => (hz s (Ioo_subset_Icc_self hs)).hasDerivAt (Icc_mem_nhds hs.1 hs.2)
    have hτz : (τ : ℝ) ∈ Ioo ((τ : ℝ) - ε) ((τ : ℝ) + ε) :=
      ⟨by linarith, by linarith⟩
    have hlip : ∀ s ∈ D ∩ Ioo ((τ : ℝ) - ε) ((τ : ℝ) + ε), ∀ x ∈ U,
        ∃ (r δ : ℝ) (K : ℝ≥0), 0 < r ∧ 0 < δ ∧
          ∀ v ∈ Ioo (s - δ) (s + δ), LipschitzOnWith K (f v) (closedBall x r) := by
      intro s _ x hx
      obtain ⟨r, δ, K, hr, hδ, hK⟩ := hlocal s x hx
      exact ⟨r, δ, K, hr, hδ, fun v hv => hK v (Ioo_subset_Icc_self hv)⟩
    have heq : EqOn y z (D ∩ Ioo ((τ : ℝ) - ε) ((τ : ℝ) + ε)) :=
      solution_eqOn_of_locally_lipschitz (hD.inter isOpen_Ioo)
        (hcD.inter ordConnected_Ioo).isPreconnected ⟨hτ, hτz⟩ hlip
        (fun s hs => hy s hs.1) (fun s hs => hz' s hs.2)
        (fun _ hs => hyU hs.1) (fun _ hs => hzU (Ioo_subset_Icc_self hs.2)) hz₀.symm
    obtain ⟨w, hwy, _, hw, hwU⟩ := patch_solutions hD isOpen_Ioo hy hz' hyU
      (fun _ hs => hzU (Ioo_subset_Icc_self hs)) heq
    have hcunion : OrdConnected (D ∪ Ioo ((τ : ℝ) - ε) ((τ : ℝ) + ε)) :=
      (hcD.isPreconnected.union (τ : ℝ) hτ hτz ordConnected_Ioo.isPreconnected).ordConnected
    have hdom := hmax _ w (hD.union isOpen_Ioo) hcunion (Or.inl ha) (hwy ha) hw hwU
    exact hdom (Or.inr ⟨by linarith [(abs_lt.mp hτabs).2],
      by linarith [(abs_lt.mp hτabs).1]⟩)
  have hall := (show IsClopen {t : Icc a b | (t : ℝ) ∈ D} from ⟨hclosed, hopen⟩).eq_univ
    ⟨⟨a, le_rfl, hab⟩, ha⟩
  intro t ht
  have : (⟨t, ht⟩ : Icc a b) ∈ {t : Icc a b | (t : ℝ) ∈ D} := by rw [hall]; trivial
  exact this

end EmcsfAcExtension.ODE
