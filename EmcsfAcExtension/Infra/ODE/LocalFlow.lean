/- Copyright (c) 2026. All rights reserved. -/

module

public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Analysis.ODE.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Local ODE solutions in an open state domain

Abstract infrastructure for internal project record (internal project record, `eq:co-static` and
`eq:co-static-outer`). The state space and parameters carry no field equations.
Solutions are existential witnesses, with their state bounds retained.
-/

public section

open Set Metric Filter
open scoped Topology NNReal

namespace EmcsfAcExtension.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Picard–Lindelöf with the closed state ball retained in the conclusion.
The time, radius, speed bound `L` and state Lipschitz bound `K` are explicit.
No solution is selected before existence is proved. -/
theorem exists_solution_closedBall [CompleteSpace E]
    {f : ℝ → E → E} {a b : ℝ} {t₀ : Icc a b} {c x : E} {R r L K : ℝ≥0}
    (hf : IsPicardLindelof f t₀ c R r L K) (hx : x ∈ closedBall c r) :
    ∃ y : ℝ → E, y t₀ = x ∧ IsIntegralCurveOn y f (Icc a b) ∧
      MapsTo y (Icc a b) (closedBall c R) := by
  obtain ⟨y, hy⟩ := _root_.ODE.FunSpace.exists_isFixedPt_next hf hx
  refine ⟨y.compProj, ?_, ?_, fun _ _ => y.compProj_mem_closedBall hf.mul_max_le⟩
  · rw [_root_.ODE.FunSpace.compProj_val, ← hy, _root_.ODE.FunSpace.next_apply₀]
  · intro t ht
    apply _root_.ODE.hasDerivWithinAt_picard_Icc t₀.2 hf.continuousOn_uncurry
      y.continuous_compProj.continuousOn
      (fun _ _ => y.compProj_mem_closedBall hf.mul_max_le) x ht |>.congr_of_mem _ ht
    intro s hs
    nth_rw 1 [← hy]
    rw [_root_.ODE.FunSpace.compProj_of_mem hs, _root_.ODE.FunSpace.next_apply]

/-- Local existence uniformly in the parameter and in a smaller ball of initial states.
The time depends only on the displayed neighborhood width, radius and speed bound;
it is independent of the parameter and the initial state within the smaller ball. -/
theorem exists_uniform_local_solution [CompleteSpace E]
    {P : Type*} (F : ℝ → P → E → E) (S : Set P) (U : Set E)
    (t₀ : ℝ) (c : E) (R : ℝ≥0) (hR : 0 < R) (δ : ℝ) (hδ : 0 < δ)
    (L K : ℝ≥0) (hU : closedBall c R ⊆ U)
    (hLip : ∀ p ∈ S, ∀ t ∈ Icc (t₀ - δ) (t₀ + δ),
      LipschitzOnWith K (F t p) (closedBall c R))
    (hcont : ∀ p ∈ S, ∀ x ∈ closedBall c R,
      ContinuousOn (fun t => F t p x) (Icc (t₀ - δ) (t₀ + δ)))
    (hbound : ∀ p ∈ S, ∀ t ∈ Icc (t₀ - δ) (t₀ + δ),
      ∀ x ∈ closedBall c R, ‖F t p x‖ ≤ L) :
    ∃ ε > 0, ∀ τ ∈ Icc (t₀ - ε) (t₀ + ε), ∀ p ∈ S,
      ∀ x ∈ closedBall c (R / 2 : ℝ≥0),
      ∃ y : ℝ → E, y τ = x ∧
        IsIntegralCurveOn y (fun t => F t p) (Icc (τ - ε) (τ + ε)) ∧
        MapsTo y (Icc (τ - ε) (τ + ε)) U := by
  let ε := min (δ / 2) ((R : ℝ) / (2 * ((L : ℝ) + 1)))
  have hε : 0 < ε := lt_min (half_pos hδ) (by positivity)
  have hεδ : ε ≤ δ / 2 := min_le_left _ _
  refine ⟨ε, hε, fun τ hτ p hp x hx => ?_⟩
  have hsub : Icc (τ - ε) (τ + ε) ⊆ Icc (t₀ - δ) (t₀ + δ) :=
    Icc_subset_Icc (by linarith [hτ.1]) (by linarith [hτ.2])
  have htime : (L : ℝ) * ε ≤ R - (R / 2 : ℝ≥0) := by
    have hL : 0 ≤ (L : ℝ) := L.coe_nonneg
    calc
      (L : ℝ) * ε ≤ L * ((R : ℝ) / (2 * ((L : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hL
      _ ≤ (R : ℝ) / 2 := by
        apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
        have hpos : 0 < (L : ℝ) + 1 := by positivity
        field_simp
        nlinarith only [hL, R.coe_nonneg]
      _ = R - (R / 2 : ℝ≥0) := by push_cast; ring
  have hf : IsPicardLindelof (fun t => F t p)
      (tmin := τ - ε) (tmax := τ + ε) ⟨τ, by constructor <;> linarith⟩
      c R (R / 2) L K := {
    lipschitzOnWith := fun t ht => hLip p hp t (hsub ht)
    continuousOn := fun z hz => (hcont p hp z hz).mono hsub
    norm_le := fun t ht z hz => hbound p hp t (hsub ht) z hz
    mul_max_le := by simpa only [add_sub_cancel_left, sub_sub_cancel, max_self] using htime }
  obtain ⟨y, hy₀, hy, hyr⟩ := exists_solution_closedBall hf hx
  exact ⟨y, hy₀, hy, fun t ht => hU (hyr ht)⟩

private theorem finset_exists_pos_le {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i, 0 < f i) : ∃ ε > 0, ∀ i ∈ s, ε ≤ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨ε, hε, hle⟩ := ih
    refine ⟨min (f i) ε, lt_min (hf i) hε, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hle j hj)

/-- A common existence time for compact initial states, also uniform in the initial time
near `t₀` and in every parameter in `S`. Local bounds are uniform in `S`;
the resulting time depends only on these local bounds and the compact set `C`.
No compactness or Lipschitz assumption on the parameter space is needed once these
uniform local bounds have been supplied. -/
theorem exists_uniform_local_solution_of_isCompact [CompleteSpace E]
    {P : Type*} (F : ℝ → P → E → E) (S : Set P) (U C : Set E)
    (t₀ : ℝ) (hC : IsCompact C)
    (hlocal : ∀ c ∈ C, ∃ (R : ℝ≥0) (δ : ℝ) (L K : ℝ≥0),
      0 < R ∧ 0 < δ ∧ closedBall c R ⊆ U ∧
      (∀ p ∈ S, ∀ t ∈ Icc (t₀ - δ) (t₀ + δ),
        LipschitzOnWith K (F t p) (closedBall c R)) ∧
      (∀ p ∈ S, ∀ x ∈ closedBall c R,
        ContinuousOn (fun t => F t p x) (Icc (t₀ - δ) (t₀ + δ))) ∧
      (∀ p ∈ S, ∀ t ∈ Icc (t₀ - δ) (t₀ + δ),
        ∀ x ∈ closedBall c R, ‖F t p x‖ ≤ L)) :
    ∃ ε > 0, ∀ τ ∈ Icc (t₀ - ε) (t₀ + ε), ∀ p ∈ S, ∀ x ∈ C,
      ∃ y : ℝ → E, y τ = x ∧
        IsIntegralCurveOn y (fun t => F t p) (Icc (τ - ε) (τ + ε)) ∧
        MapsTo y (Icc (τ - ε) (τ + ε)) U := by
  classical
  choose R δ L K hR hδ hU hLip hcont hbound using fun c : C => hlocal c c.2
  have hex (c : C) := exists_uniform_local_solution F S U t₀ c (R c) (hR c)
    (δ c) (hδ c) (L c) (K c) (hU c) (hLip c) (hcont c) (hbound c)
  choose ε hε hsol using hex
  obtain ⟨s, hs⟩ := hC.elim_finite_subcover
    (fun c : C => ball (c : E) ((R c : ℝ) / 2))
    (fun _ => isOpen_ball) (by
      intro c hc
      exact mem_iUnion.mpr ⟨⟨c, hc⟩, mem_ball_self (by exact half_pos (hR ⟨c, hc⟩))⟩)
  obtain ⟨η, hη, hηle⟩ := finset_exists_pos_le s ε hε
  refine ⟨η, hη, fun τ hτ p hp x hx => ?_⟩
  obtain ⟨c, hcs, hxc⟩ := mem_iUnion₂.mp (hs hx)
  have hηc := hηle c hcs
  have hτc : τ ∈ Icc (t₀ - ε c) (t₀ + ε c) :=
    ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  have hxc' : x ∈ closedBall (c : E) (R c / 2 : ℝ≥0) := by
    simpa only [NNReal.coe_div, NNReal.coe_ofNat] using mem_closedBall.mpr hxc.le
  obtain ⟨y, hy₀, hy, hyU⟩ := hsol c τ hτc p hp x hxc'
  have hsub : Icc (τ - η) (τ + η) ⊆ Icc (τ - ε c) (τ + ε c) :=
    Icc_subset_Icc (by linarith) (by linarith)
  exact ⟨y, hy₀, hy.mono hsub, fun t ht => hyU (hsub ht)⟩

/-- Local uniqueness from a state Lipschitz bound on a time/state neighborhood.
Only local bounds at the common initial state are required. -/
theorem solution_eventuallyEq {f : ℝ → E → E} {D : Set ℝ} {y z : ℝ → E}
    {t₀ : ℝ} {r δ : ℝ} {K : ℝ≥0} (hr : 0 < r) (hδ : 0 < δ)
    (hD : D ∈ 𝓝 t₀)
    (hLip : ∀ t ∈ Ioo (t₀ - δ) (t₀ + δ),
      LipschitzOnWith K (f t) (closedBall (y t₀) r))
    (hy : ∀ t ∈ D, HasDerivAt y (f t (y t)) t)
    (hz : ∀ t ∈ D, HasDerivAt z (f t (z t)) t)
    (h₀ : y t₀ = z t₀) : y =ᶠ[𝓝 t₀] z := by
  have hyc := (hy t₀ (mem_of_mem_nhds hD)).continuousAt
  have hzc := (hz t₀ (mem_of_mem_nhds hD)).continuousAt
  have hyr : ∀ᶠ t in 𝓝 t₀, y t ∈ closedBall (y t₀) r :=
    hyc.preimage_mem_nhds (closedBall_mem_nhds _ hr)
  have hzr : ∀ᶠ t in 𝓝 t₀, z t ∈ closedBall (y t₀) r := by
    rw [h₀]
    exact hzc.preimage_mem_nhds (closedBall_mem_nhds _ hr)
  apply ODE_solution_unique_of_eventually (K := K) (s := fun _ => closedBall (y t₀) r)
  · have hi : Ioo (t₀ - δ) (t₀ + δ) ∈ 𝓝 t₀ :=
      Ioo_mem_nhds (by linarith) (by linarith)
    filter_upwards [hi] with t ht
    exact hLip t ht
  · filter_upwards [hD, hyr] with t ht htr
    exact ⟨hy t ht, htr⟩
  · filter_upwards [hD, hzr] with t ht htr
    exact ⟨hz t ht, htr⟩
  · exact h₀

/-- Uniqueness on any connected open time domain for a vector field locally
Lipschitz in the state, uniformly on a neighborhood of each time/state point.
The local constants may vary with both the time and state. -/
theorem solution_eqOn_of_locally_lipschitz {f : ℝ → E → E} {D : Set ℝ} {U : Set E}
    {y z : ℝ → E} {t₀ : ℝ} (hD : IsOpen D) (hcD : IsPreconnected D) (ht₀ : t₀ ∈ D)
    (hlocal : ∀ t ∈ D, ∀ x ∈ U, ∃ (r δ : ℝ) (K : ℝ≥0),
      0 < r ∧ 0 < δ ∧ ∀ s ∈ Ioo (t - δ) (t + δ),
        LipschitzOnWith K (f s) (closedBall x r))
    (hy : ∀ t ∈ D, HasDerivAt y (f t (y t)) t)
    (hz : ∀ t ∈ D, HasDerivAt z (f t (z t)) t)
    (hyU : MapsTo y D U) (_hzU : MapsTo z D U) (h₀ : y t₀ = z t₀) : EqOn y z D := by
  let : PreconnectedSpace D := Subtype.preconnectedSpace hcD
  have hyc : Continuous (fun t : D => y t) :=
    continuousOn_iff_continuous_domRestrict.mp (HasDerivAt.continuousOn hy)
  have hzc : Continuous (fun t : D => z t) :=
    continuousOn_iff_continuous_domRestrict.mp (HasDerivAt.continuousOn hz)
  have hclosed : IsClosed {t : D | y t = z t} := isClosed_eq hyc hzc
  have hopen : IsOpen {t : D | y t = z t} := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    obtain ⟨r, δ, K, hr, hδ, hLip⟩ := hlocal t t.2 (y t) (hyU t.2)
    have heq := solution_eventuallyEq hr hδ (hD.mem_nhds t.2) hLip hy hz ht
    exact continuous_subtype_val.continuousAt.preimage_mem_nhds heq
  have hall := (show IsClopen {t : D | y t = z t} from ⟨hclosed, hopen⟩).eq_univ
    ⟨⟨t₀, ht₀⟩, h₀⟩
  intro t ht
  have : (⟨t, ht⟩ : D) ∈ {t : D | y t = z t} := by rw [hall]; trivial
  exact this

/-- Joint continuity and locally uniform state Lipschitz bounds give quantitative
local boxes uniform over a compact parameter set. The radius, time width, speed
bound and Lipschitz bound depend on the center, field, domain and parameter set. -/
theorem exists_local_bounds_of_isCompact [FiniteDimensional ℝ E]
    {P : Type*} [TopologicalSpace P] {F : ℝ → P → E → E} {S : Set P} {U : Set E}
    (hS : IsCompact S) (hU : IsOpen U)
    (hcont : ContinuousOn (fun w : ℝ × P × E => F w.1 w.2.1 w.2.2)
      (univ ×ˢ S ×ˢ U)) (t₀ : ℝ) (x : E) (hx : x ∈ U)
    (hlocal : ∀ p ∈ S, ∃ (V : Set P) (r δ : ℝ) (K : ℝ≥0),
      IsOpen V ∧ p ∈ V ∧ 0 < r ∧ 0 < δ ∧
      ∀ q ∈ S ∩ V, ∀ t ∈ Icc (t₀ - δ) (t₀ + δ),
        LipschitzOnWith K (F t q) (closedBall x r)) :
    ∃ (R : ℝ≥0) (δ : ℝ) (L K : ℝ≥0),
      0 < R ∧ 0 < δ ∧ closedBall x R ⊆ U ∧
      (∀ p ∈ S, ∀ t ∈ Icc (t₀ - δ) (t₀ + δ),
        LipschitzOnWith K (F t p) (closedBall x R)) ∧
      (∀ p ∈ S, ∀ z ∈ closedBall x R,
        ContinuousOn (fun t => F t p z) (Icc (t₀ - δ) (t₀ + δ))) ∧
      (∀ p ∈ S, ∀ t ∈ Icc (t₀ - δ) (t₀ + δ),
        ∀ z ∈ closedBall x R, ‖F t p z‖ ≤ L) := by
  classical
  choose V r δ K hV hpV hr hδ hLip using fun p : S => hlocal p p.2
  obtain ⟨s, hs⟩ := hS.elim_finite_subcover V hV (by
    intro p hp
    exact mem_iUnion.mpr ⟨⟨p, hp⟩, hpV ⟨p, hp⟩⟩)
  obtain ⟨η, hη, hηle⟩ := finset_exists_pos_le s (fun p => min (r p) (δ p))
    (fun p => lt_min (hr p) (hδ p))
  obtain ⟨d, hd, hdu⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  let R : ℝ≥0 := ⟨min (d / 2) η, (lt_min (half_pos hd) hη).le⟩
  have hR : 0 < R := lt_min (half_pos hd) hη
  have hRU : closedBall x R ⊆ U := by
    intro z hz
    apply hdu
    exact (mem_closedBall.mp hz).trans_lt ((min_le_left _ _).trans_lt (half_lt_self hd))
  have hK : ∀ p ∈ S, ∀ t ∈ Icc (t₀ - η) (t₀ + η),
      LipschitzOnWith (s.sup K) (F t p) (closedBall x R) := by
    intro p hp t ht
    obtain ⟨q, hqs, hpq⟩ := mem_iUnion₂.mp (hs hp)
    have hηr : η ≤ r q := (hηle q hqs).trans (min_le_left _ _)
    have hηδ : η ≤ δ q := (hηle q hqs).trans (min_le_right _ _)
    have htq : t ∈ Icc (t₀ - δ q) (t₀ + δ q) :=
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact ((hLip q p ⟨hp, hpq⟩ t htq).mono
      (closedBall_subset_closedBall ((min_le_right _ _).trans hηr))).weaken
      (Finset.le_sup hqs)
  have hbox : ContinuousOn (fun w : ℝ × P × E => F w.1 w.2.1 w.2.2)
      (Icc (t₀ - η) (t₀ + η) ×ˢ S ×ˢ closedBall x R) :=
    hcont.mono (prod_mono (subset_univ _) (prod_mono Subset.rfl hRU))
  obtain ⟨B, hB⟩ := IsCompact.exists_bound_of_continuousOn
    (isCompact_Icc.prod (hS.prod (isCompact_closedBall x (R : ℝ)))) hbox
  refine ⟨R, η, ⟨max B 0, le_max_right _ _⟩, s.sup K, hR, hη, hRU, hK, ?_, ?_⟩
  · intro p hp z hz
    exact hbox.comp (continuousOn_id.prodMk (continuousOn_const.prodMk continuousOn_const))
      (fun t ht => ⟨ht, hp, hz⟩)
  · intro p hp t ht z hz
    exact (hB (t, p, z) ⟨ht, hp, hz⟩).trans (le_max_left _ _)

/-- Local existence for continuous, locally state Lipschitz fields, with a time
uniform over compact parameter and initial-state sets. Initial times may vary near
`t₀`, including `t₀ = 0`; all constants precede the actual initial data. -/
theorem exists_uniform_local_solution_of_continuousOn [FiniteDimensional ℝ E]
    {P : Type*} [TopologicalSpace P] {F : ℝ → P → E → E} {S : Set P} {U C : Set E}
    (hS : IsCompact S) (hU : IsOpen U) (hC : IsCompact C) (hCU : C ⊆ U)
    (hcont : ContinuousOn (fun w : ℝ × P × E => F w.1 w.2.1 w.2.2)
      (univ ×ˢ S ×ˢ U)) (t₀ : ℝ)
    (hlocal : ∀ x ∈ U, ∀ p ∈ S, ∃ (V : Set P) (r δ : ℝ) (K : ℝ≥0),
      IsOpen V ∧ p ∈ V ∧ 0 < r ∧ 0 < δ ∧
      ∀ q ∈ S ∩ V, ∀ t ∈ Icc (t₀ - δ) (t₀ + δ),
        LipschitzOnWith K (F t q) (closedBall x r)) :
    ∃ ε > 0, ∀ τ ∈ Icc (t₀ - ε) (t₀ + ε), ∀ p ∈ S, ∀ x ∈ C,
      ∃ y : ℝ → E, y τ = x ∧
        IsIntegralCurveOn y (fun t => F t p) (Icc (τ - ε) (τ + ε)) ∧
        MapsTo y (Icc (τ - ε) (τ + ε)) U := by
  apply exists_uniform_local_solution_of_isCompact F S U C t₀ hC
  intro c hc
  exact exists_local_bounds_of_isCompact hS hU hcont t₀ c (hCU hc) (hlocal c (hCU hc))

/-- A local solution through a prescribed point of the open state domain.
Its time depends on the local field bounds at that point. -/
theorem exists_local_solution [FiniteDimensional ℝ E]
    {f : ℝ → E → E} {U : Set E} (hU : IsOpen U)
    (hcont : ContinuousOn (Function.uncurry f) (univ ×ˢ U)) (t₀ : ℝ) (x₀ : E)
    (hx₀ : x₀ ∈ U)
    (hlocal : ∀ x ∈ U, ∃ (r δ : ℝ) (K : ℝ≥0), 0 < r ∧ 0 < δ ∧
      ∀ s ∈ Icc (t₀ - δ) (t₀ + δ), LipschitzOnWith K (f s) (closedBall x r)) :
    ∃ ε > 0, ∃ y : ℝ → E, y t₀ = x₀ ∧
      (∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt y (f t (y t)) t) ∧
      MapsTo y (Ioo (t₀ - ε) (t₀ + ε)) U := by
  have hc : ContinuousOn (fun w : ℝ × Unit × E => f w.1 w.2.2)
      (univ ×ˢ ({()} : Set Unit) ×ˢ U) :=
    hcont.comp (continuousOn_fst.prodMk continuousOn_snd.snd)
      (fun _ hw => ⟨trivial, hw.2.2⟩)
  have hl : ∀ x ∈ U, ∀ p ∈ ({()} : Set Unit),
      ∃ (V : Set Unit) (r δ : ℝ) (K : ℝ≥0), IsOpen V ∧ p ∈ V ∧ 0 < r ∧ 0 < δ ∧
        ∀ q ∈ ({()} : Set Unit) ∩ V, ∀ t ∈ Icc (t₀ - δ) (t₀ + δ),
          LipschitzOnWith K (f t) (closedBall x r) := by
    intro x hx p hp
    obtain ⟨r, δ, K, hr, hδ, hK⟩ := hlocal x hx
    exact ⟨univ, r, δ, K, isOpen_univ, trivial, hr, hδ, fun _ _ => hK⟩
  obtain ⟨ε, hε, hsol⟩ := exists_uniform_local_solution_of_continuousOn
    isCompact_singleton hU isCompact_singleton (singleton_subset_iff.mpr hx₀) hc t₀ hl
  obtain ⟨y, hy₀, hy, hyU⟩ := hsol t₀ ⟨by linarith, by linarith⟩ () rfl x₀ rfl
  exact ⟨ε, hε, y, hy₀, fun t ht => (hy t (Ioo_subset_Icc_self ht)).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2), fun _ ht => hyU (Ioo_subset_Icc_self ht)⟩

private theorem exists_bound_of_isCompact_of_locally_bounded
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsCompact A) (f : X → ℝ)
    (hf : ∀ x ∈ A, ∃ B : ℝ, ∀ᶠ z in 𝓝[A] x, f z ≤ B) :
    ∃ B : ℝ, ∀ x ∈ A, f x ≤ B := by
  classical
  have hex (x : A) : ∃ (B : ℝ) (O : Set X), IsOpen O ∧ (x : X) ∈ O ∧
      ∀ z ∈ O ∩ A, f z ≤ B := by
    obtain ⟨B, hB⟩ := hf x x.2
    obtain ⟨O, hO, hxO, hOB⟩ := mem_nhdsWithin.mp hB
    exact ⟨B, O, hO, hxO, fun z hz => hOB hz⟩
  choose B O hO hxO hOB using hex
  obtain ⟨s, hs⟩ := hA.elim_finite_subcover O hO
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxO ⟨x, hx⟩⟩)
  obtain ⟨M, hM⟩ := (s.image B).finite_toSet.bddAbove
  refine ⟨M, fun x hx => ?_⟩
  obtain ⟨z, hzs, hxz⟩ := mem_iUnion₂.mp (hs hx)
  exact (hOB z x ⟨hxz, hx⟩).trans (hM (Finset.mem_image.mpr ⟨z, hzs, rfl⟩))

/-- Uniform local existence for a single field over compact initial states and
nearby initial times. The common time depends only on the field, domain, compact
state set and center time. -/
theorem exists_uniform_local_solution_scalar [FiniteDimensional ℝ E]
    {f : ℝ → E → E} {U C : Set E} (hU : IsOpen U) (hC : IsCompact C) (hCU : C ⊆ U)
    (hcont : ContinuousOn (Function.uncurry f) (univ ×ˢ U)) (t₀ : ℝ)
    (hlocal : ∀ x ∈ U, ∃ (r δ : ℝ) (K : ℝ≥0), 0 < r ∧ 0 < δ ∧
      ∀ s ∈ Icc (t₀ - δ) (t₀ + δ), LipschitzOnWith K (f s) (closedBall x r)) :
    ∃ ε > 0, ∀ τ ∈ Icc (t₀ - ε) (t₀ + ε), ∀ x ∈ C,
      ∃ y : ℝ → E, y τ = x ∧ IsIntegralCurveOn y f (Icc (τ - ε) (τ + ε)) ∧
        MapsTo y (Icc (τ - ε) (τ + ε)) U := by
  have hc : ContinuousOn (fun w : ℝ × Unit × E => f w.1 w.2.2)
      (univ ×ˢ ({()} : Set Unit) ×ˢ U) :=
    hcont.comp (continuousOn_fst.prodMk continuousOn_snd.snd)
      (fun _ hw => ⟨trivial, hw.2.2⟩)
  have hl : ∀ x ∈ U, ∀ p ∈ ({()} : Set Unit),
      ∃ (V : Set Unit) (r δ : ℝ) (K : ℝ≥0), IsOpen V ∧ p ∈ V ∧ 0 < r ∧ 0 < δ ∧
        ∀ q ∈ ({()} : Set Unit) ∩ V, ∀ t ∈ Icc (t₀ - δ) (t₀ + δ),
          LipschitzOnWith K (f t) (closedBall x r) := by
    intro x hx p _
    obtain ⟨r, δ, K, hr, hδ, hK⟩ := hlocal x hx
    exact ⟨univ, r, δ, K, isOpen_univ, trivial, hr, hδ, fun _ _ => hK⟩
  obtain ⟨ε, hε, hsol⟩ := exists_uniform_local_solution_of_continuousOn
    isCompact_singleton hU hC hCU hc t₀ hl
  exact ⟨ε, hε, fun τ hτ x hx => hsol τ hτ () rfl x hx⟩

omit [NormedSpace ℝ E] in
/-- Uniform state Lipschitz bound on compact time, parameter and state sets.
Only the state variable is Lipschitz; the field and parameter dependence are
continuous. The local state Lipschitz bounds are uniform on parameter/time
neighborhoods. The resulting constant depends on the three compact sets and field. -/
theorem exists_uniform_lipschitzOnWith_of_isCompact
    {P : Type*} [TopologicalSpace P] {F : ℝ → P → E → E} {S : Set P}
    {U C : Set E} {a b : ℝ} (hS : IsCompact S) (hC : IsCompact C) (hCU : C ⊆ U)
    (hcont : ContinuousOn (fun w : ℝ × P × E => F w.1 w.2.1 w.2.2) (univ ×ˢ S ×ˢ U))
    (hlocal : ∀ t ∈ Icc a b, ∀ p ∈ S, ∀ x ∈ C,
      ∃ (V : Set P) (r δ : ℝ) (K : ℝ≥0), IsOpen V ∧ p ∈ V ∧ 0 < r ∧ 0 < δ ∧
        ∀ q ∈ S ∩ V, ∀ s ∈ Icc (t - δ) (t + δ),
          LipschitzOnWith K (F s q) (closedBall x r)) :
    ∃ K : ℝ≥0, ∀ p ∈ S, ∀ t ∈ Icc a b, LipschitzOnWith K (F t p) C := by
  let A := Icc a b ×ˢ S ×ˢ C ×ˢ C
  let Q := fun w : ℝ × P × E × E =>
    dist (F w.1 w.2.1 w.2.2.1) (F w.1 w.2.1 w.2.2.2) / dist w.2.2.1 w.2.2.2
  have hA : IsCompact A := isCompact_Icc.prod (hS.prod (hC.prod hC))
  have hbounded : ∀ w ∈ A, ∃ B : ℝ, ∀ᶠ z in 𝓝[A] w, Q z ≤ B := by
    intro w hw
    by_cases heq : w.2.2.1 = w.2.2.2
    · obtain ⟨V, r, δ, K, hV, hpV, hr, hδ, hK⟩ :=
        hlocal w.1 hw.1 w.2.1 hw.2.1 w.2.2.1 hw.2.2.1
      have ht : ∀ᶠ z : ℝ × P × E × E in 𝓝 w, z.1 ∈ Icc (w.1 - δ) (w.1 + δ) :=
        continuous_fst.continuousAt.preimage_mem_nhds
          (Icc_mem_nhds (by linarith) (by linarith))
      have hp : ∀ᶠ z : ℝ × P × E × E in 𝓝 w, z.2.1 ∈ V :=
        continuous_snd.fst.continuousAt.preimage_mem_nhds (hV.mem_nhds hpV)
      have hx : ∀ᶠ z : ℝ × P × E × E in 𝓝 w, z.2.2.1 ∈ closedBall w.2.2.1 r :=
        continuous_snd.snd.fst.continuousAt.preimage_mem_nhds (closedBall_mem_nhds _ hr)
      have hz : ∀ᶠ z : ℝ × P × E × E in 𝓝 w, z.2.2.2 ∈ closedBall w.2.2.1 r := by
        rw [heq]
        exact continuous_snd.snd.snd.continuousAt.preimage_mem_nhds (closedBall_mem_nhds _ hr)
      refine ⟨K, ?_⟩
      filter_upwards [ht.filter_mono nhdsWithin_le_nhds,
        hp.filter_mono nhdsWithin_le_nhds, hx.filter_mono nhdsWithin_le_nhds,
        hz.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hzt hzp hzx hzz hzA
      exact div_le_of_le_mul₀ dist_nonneg K.coe_nonneg
        ((hK z.2.1 ⟨hzA.2.1, hzp⟩ z.1 hzt).dist_le_mul z.2.2.1 hzx z.2.2.2 hzz)
    · have hf₁ : ContinuousWithinAt
          (fun z : ℝ × P × E × E => F z.1 z.2.1 z.2.2.1) A w :=
        hcont.comp (continuousOn_fst.prodMk (continuousOn_snd.fst.prodMk continuousOn_snd.snd.fst))
          (fun _ hz => ⟨trivial, hz.2.1, hCU hz.2.2.1⟩) w hw
      have hf₂ : ContinuousWithinAt
          (fun z : ℝ × P × E × E => F z.1 z.2.1 z.2.2.2) A w :=
        hcont.comp (continuousOn_fst.prodMk (continuousOn_snd.fst.prodMk continuousOn_snd.snd.snd))
          (fun _ hz => ⟨trivial, hz.2.1, hCU hz.2.2.2⟩) w hw
      have hQ : ContinuousWithinAt Q A w := (hf₁.dist hf₂).div
        (continuous_snd.snd.fst.dist continuous_snd.snd.snd).continuousWithinAt
        (dist_ne_zero.mpr heq)
      have he : ∀ᶠ z in 𝓝[A] w, Q z < Q w + 1 :=
        hQ.preimage_mem_nhdsWithin (Iio_mem_nhds (lt_add_one (Q w)))
      exact ⟨Q w + 1, he.mono fun _ hz => hz.le⟩
  obtain ⟨B, hB⟩ := exists_bound_of_isCompact_of_locally_bounded hA Q hbounded
  refine ⟨⟨max B 0, le_max_right _ _⟩, fun p hp t ht => LipschitzOnWith.of_dist_le_mul ?_⟩
  intro x hx z hz
  by_cases heq : x = z
  · simp only [heq, dist_self, mul_zero, le_refl]
  · exact (div_le_iff₀ (dist_pos.mpr heq)).mp
      ((hB (t, p, x, z) ⟨ht, hp, hx, hz⟩).trans (le_max_left B 0))

end EmcsfAcExtension.ODE
