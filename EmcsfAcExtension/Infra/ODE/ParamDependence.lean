/- Copyright (c) 2026. All rights reserved. -/

module

public import EmcsfAcExtension.Infra.ODE.Continuation
public import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Dependence on ODE data and compact strict barriers

internal project record infrastructure for the compact static family in internal project record.
Parameter errors enter through uniform continuity of the field, with no
parameter Lipschitz hypothesis. Time translation treats continuously varying
initial times, including zero. Strict barriers retain their own stopping times.
-/

public section

open Set Metric Filter
open scoped Topology NNReal

namespace EmcsfAcExtension.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Grönwall comparison for two parameters and initial values on a common time
interval. `K` is the state Lipschitz bound for the first field, and `ε` bounds
the parameter perturbation along the second trajectory. Every coefficient is
explicit, uniformly in both solutions and parameters. -/
theorem dist_le_gronwallBound_of_parameters
    {P : Type*} {F : ℝ → P → E → E} {p q : P} {U : Set E}
    {a b ε δ : ℝ} {K : ℝ≥0} {y z : ℝ → E}
    (hK : ∀ t ∈ Icc a b, LipschitzOnWith K (F t p) U)
    (hy : IsIntegralCurveOn y (fun t => F t p) (Icc a b))
    (hz : IsIntegralCurveOn z (fun t => F t q) (Icc a b))
    (hyU : MapsTo y (Icc a b) U) (hzU : MapsTo z (Icc a b) U)
    (herror : ∀ t ∈ Icc a b, dist (F t q (z t)) (F t p (z t)) ≤ ε)
    (hinit : dist (y a) (z a) ≤ δ) :
    ∀ t ∈ Icc a b, dist (y t) (z t) ≤ gronwallBound δ K ε (t - a) := by
  have h := dist_le_of_approx_trajectories_ODE_of_mem
    (fun t ht => hK t (Ico_subset_Icc_self ht)) hy.continuousOn
    (fun t ht => (hy t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc ht.1 le_rfl)))
    (by intro t ht; simp only [dist_self, le_refl] :
      ∀ t ∈ Ico a b, dist (F t p (y t)) (F t p (y t)) ≤ 0)
    (fun _ ht => hyU (Ico_subset_Icc_self ht)) hz.continuousOn
    (fun t ht => (hz t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc ht.1 le_rfl)))
    (fun t ht => herror t (Ico_subset_Icc_self ht))
    (fun _ ht => hzU (Ico_subset_Icc_self ht)) hinit
  simpa only [zero_add] using h

/-- Uniform dependence on parameter and initial value for solutions in a compact
state set. Local constants `K` may depend on the base parameter, field, state set
and time interval, but are uniform in time and both compared trajectories.
The parameter space need only be a topological space. -/
theorem tendstoUniformlyOn_solution_of_continuousOn
    {P : Type*} [TopologicalSpace P] {F : ℝ → P → E → E}
    {S : Set P} {C : Set E} {a b : ℝ} {y : P → ℝ → E} (_hab : a ≤ b)
    (hC : IsCompact C)
    (hcont : ContinuousOn (fun w : P × (ℝ × E) => F w.2.1 w.1 w.2.2)
      (S ×ˢ (Icc a b ×ˢ C)))
    (hLip : ∀ p ∈ S, ∃ K : ℝ≥0, ∀ t ∈ Icc a b,
      LipschitzOnWith K (F t p) C)
    (hsol : ∀ p ∈ S, IsIntegralCurveOn (y p) (fun t => F t p) (Icc a b))
    (hmem : ∀ p ∈ S, MapsTo (y p) (Icc a b) C)
    (hinit : ContinuousOn (fun p => y p a) S) {p₀ : P} (hp₀ : p₀ ∈ S) :
    TendstoUniformlyOn y (y p₀) (𝓝[S] p₀) (Icc a b) := by
  obtain ⟨K, hK⟩ := hLip p₀ hp₀
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hc : ContinuousAt (fun η : ℝ => gronwallBound η K η (b - a)) 0 := by
    unfold gronwallBound
    split_ifs <;> fun_prop
  have hc₀ : gronwallBound 0 K 0 (b - a) = 0 := gronwallBound_ε0_δ0 _ _
  have hsmall : ∀ᶠ η : ℝ in 𝓝 0, gronwallBound η K η (b - a) < ε :=
    hc.preimage_mem_nhds (Iio_mem_nhds (by simpa only [hc₀] using hε))
  obtain ⟨r, hr, hsmallr⟩ := Metric.eventually_nhds_iff_ball.mp hsmall
  let η := r / 2
  have hη : 0 < η := half_pos hr
  have hηsmall : gronwallBound η K η (b - a) < ε :=
    hsmallr η (by
      simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hη]
        using (show η < r from half_lt_self hr))
  obtain ⟨V, hV, hFV⟩ := (isCompact_Icc.prod hC).mem_uniformity_of_prod
    (f := fun p z => F z.1 p z.2) hcont hp₀
    (Metric.dist_mem_uniformity hη)
  have hi : ∀ᶠ p in 𝓝[S] p₀, dist (y p a) (y p₀ a) < η :=
    (hinit p₀ hp₀).preimage_mem_nhdsWithin (ball_mem_nhds _ hη)
  filter_upwards [hV, hi, self_mem_nhdsWithin] with p hpV hpi hp
  intro t ht
  have herr : ∀ s ∈ Icc a b, dist (F s p (y p s)) (F s p₀ (y p s)) ≤ η := by
    intro s hs
    exact (hFV p hpV (s, y p s) ⟨hs, hmem p hp hs⟩).le
  have hdist := dist_le_gronwallBound_of_parameters hK (hsol p₀ hp₀) (hsol p hp)
    (hmem p₀ hp₀) (hmem p hp) herr (by simpa only [dist_comm] using hpi.le) t ht
  exact hdist.trans_lt ((gronwallBound_mono hη.le hη.le K.coe_nonneg
    (sub_le_sub_right ht.2 a)).trans_lt hηsmall)

/-- Joint continuity in the parameter and observation time of a family of ODE
solutions. The hypotheses provide a common compact state tube and a common time
interval; the initial value is allowed to depend continuously on the parameter. -/
theorem continuousOn_solution_of_continuousOn
    {P : Type*} [TopologicalSpace P] {F : ℝ → P → E → E}
    {S : Set P} {C : Set E} {a b : ℝ} {y : P → ℝ → E} (hab : a ≤ b)
    (hC : IsCompact C)
    (hcont : ContinuousOn (fun w : P × (ℝ × E) => F w.2.1 w.1 w.2.2)
      (S ×ˢ (Icc a b ×ˢ C)))
    (hLip : ∀ p ∈ S, ∃ K : ℝ≥0, ∀ t ∈ Icc a b,
      LipschitzOnWith K (F t p) C)
    (hsol : ∀ p ∈ S, IsIntegralCurveOn (y p) (fun t => F t p) (Icc a b))
    (hmem : ∀ p ∈ S, MapsTo (y p) (Icc a b) C)
    (hinit : ContinuousOn (fun p => y p a) S) :
    ContinuousOn (fun w : P × ℝ => y w.1 w.2) (S ×ˢ Icc a b) := by
  rintro ⟨p, t⟩ ⟨hp, ht⟩
  have hu := tendstoUniformlyOn_solution_of_continuousOn hab hC hcont hLip hsol hmem hinit hp
  change Tendsto (fun w : P × ℝ => y w.1 w.2) (𝓝[S ×ˢ Icc a b] (p, t))
    (𝓝 (y p t))
  rw [nhdsWithin_prod_eq]
  have hup : TendstoUniformlyOn (fun w : P × ℝ => y w.1) (y p)
      (𝓝[S] p ×ˢ 𝓝[Icc a b] t) (Icc a b) :=
    fun u hu' => tendsto_fst.eventually (hu u hu')
  exact hup.tendsto_comp ((hsol p hp).continuousOn t ht) tendsto_snd

/-- Translate a solution to elapsed time, retaining the initial point and derivative
on a common interval. This requires no positivity of the physical initial time. -/
theorem solution_time_translate {f : ℝ → E → E} {y : ℝ → E} {τ a b : ℝ}
    (hy : IsIntegralCurveOn y f (Icc (τ + a) (τ + b))) :
    IsIntegralCurveOn (fun s => y (τ + s))
      (fun s x => f (τ + s) x) (Icc a b) := by
  intro s hs
  have hmap : MapsTo (fun s : ℝ => τ + s) (Icc a b) (Icc (τ + a) (τ + b)) :=
    fun _ ht => ⟨by dsimp; linarith [ht.1], by dsimp; linarith [ht.2]⟩
  have hd := (hy (τ + s) (hmap hs)).scomp s
    ((hasDerivAt_id s).const_add τ).hasDerivWithinAt hmap
  simpa only [one_smul, Function.comp_def] using hd

omit [NormedSpace ℝ E] in
/-- A continuous initial-time shift preserves joint continuity of the vector field.
In particular `τ = L⁻¹` may tend to zero in the outer static family. -/
theorem continuousOn_time_translate
    {P : Type*} [TopologicalSpace P] {F : ℝ → P → E → E} {S : Set P} {U : Set E}
    {τ : P → ℝ} (hτ : ContinuousOn τ S)
    (hF : ContinuousOn (fun w : ℝ × P × E => F w.1 w.2.1 w.2.2)
      (univ ×ˢ S ×ˢ U)) :
    ContinuousOn (fun w : ℝ × P × E => F (τ w.2.1 + w.1) w.2.1 w.2.2)
      (univ ×ˢ S ×ˢ U) := by
  have ht : ContinuousOn (fun w : ℝ × P × E => τ w.2.1) (univ ×ˢ S ×ˢ U) :=
    hτ.comp continuousOn_snd.fst (fun _ hw => hw.2.1)
  exact hF.comp ((ht.add continuousOn_fst).prodMk
    (continuousOn_snd.fst.prodMk continuousOn_snd.snd))
    (fun _ hw => ⟨trivial, hw.2.1, hw.2.2⟩)

private theorem finset_uniform_pos {ι : Type*} (s : Finset ι) (f : ι → ℝ)
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

/-- Finite strict barriers for a compact parameter family. Each open patch can use
its own stopping time/radius `ρ i` and coefficient bound `B i`; only the positive
lower radius, strict violation margin and upper coefficient bound are uniform.
The hypotheses may encode the existence and nondegeneracy of the stopped
trajectory in `V i`. No common trajectory interval down to the smallest radius
is asserted. The constants depend only on the supplied compact family and patches. -/
theorem exists_uniform_strict_margins_of_open_cover
    {P I : Type*} [TopologicalSpace P] {S : Set P} (hS : IsCompact S)
    (V : I → Set P) (ρ B : I → ℝ) (g : I → P → ℝ)
    (hV : ∀ i, IsOpen (V i)) (hg : ∀ i, ContinuousOn (g i) (S ∩ V i))
    (hcover : ∀ p ∈ S, ∃ i, p ∈ V i ∧ 0 < ρ i ∧ 0 < g i p) :
    ∃ (s : Finset I) (r γ C : ℝ), 0 < r ∧ 0 < γ ∧ 0 < C ∧
      (∀ i ∈ s, r ≤ ρ i ∧ |B i| ≤ C) ∧
      ∀ p ∈ S, ∃ i ∈ s, p ∈ V i ∧ γ ≤ g i p := by
  classical
  choose idx hidx hρ hpos using fun p : S => hcover p p.2
  have hnb (p : S) : ∃ O : Set P, IsOpen O ∧ (p : P) ∈ O ∧
      O ∩ S ⊆ {q | q ∈ V (idx p) ∧ g (idx p) p / 2 < g (idx p) q} := by
    have he : {q | g (idx p) p / 2 < g (idx p) q} ∈ 𝓝[S ∩ V (idx p)] (p : P) :=
      (hg (idx p) p ⟨p.2, hidx p⟩).preimage_mem_nhdsWithin
        (Ioi_mem_nhds (half_lt_self (hpos p)))
    obtain ⟨O, hOo, hpO, hO⟩ := mem_nhdsWithin.mp he
    refine ⟨O ∩ V (idx p), hOo.inter (hV (idx p)), ⟨hpO, hidx p⟩, ?_⟩
    intro q hq
    exact ⟨hq.1.2, hO ⟨hq.1.1, hq.2, hq.1.2⟩⟩
  choose O hOo hpO hO using hnb
  obtain ⟨s, hs⟩ := hS.elim_finite_subcover O hOo (by
    intro p hp
    exact mem_iUnion.mpr ⟨⟨p, hp⟩, hpO ⟨p, hp⟩⟩)
  obtain ⟨r, hr, hrle⟩ := finset_uniform_pos s (fun p => ρ (idx p)) hρ
  obtain ⟨γ, hγ, hγle⟩ := finset_uniform_pos s
    (fun p => g (idx p) p / 2) (fun p => half_pos (hpos p))
  obtain ⟨C, hC⟩ := ((s.image (fun p => |B (idx p)|)).finite_toSet.union
    (Set.finite_singleton 1)).bddAbove
  have hC₀ : 0 < C := zero_lt_one.trans_le (hC (Or.inr rfl))
  refine ⟨s.image idx, r, γ, C, hr, hγ, hC₀, ?_, ?_⟩
  · intro i hi
    obtain ⟨p, hps, rfl⟩ := Finset.mem_image.mp hi
    exact ⟨hrle p hps, hC (Or.inl (Finset.mem_image.mpr ⟨p, hps, rfl⟩))⟩
  · intro p hp
    obtain ⟨q, hqs, hpq⟩ := mem_iUnion₂.mp (hs hp)
    have hq := hO q ⟨hpq, hp⟩
    exact ⟨idx q, Finset.mem_image.mpr ⟨q, hqs, rfl⟩, hq.1,
      (hγle q hqs).trans hq.2.le⟩

/-- Finite-time existence near a reference trajectory inside an open Lipschitz
tube. The tube contains the radius-`r` balls around the reference in a compact
subset `C`. The exact Grönwall smallness condition depends only on `K`, the time
interval, `r`, the initial error and the field error along the reference.
It yields existence through both endpoints, not just a conditional estimate. -/
theorem exists_solution_on_Icc_of_reference [FiniteDimensional ℝ E]
    {P : Type*} {F : ℝ → P → E → E} {p q : P} {U C : Set E}
    {a b r δ ε : ℝ} {K : ℝ≥0} {z : ℝ → E} {x : E}
    (hab : a ≤ b) (hU : IsOpen U) (hC : IsCompact C) (hCU : C ⊆ U)
    (htube : ∀ t ∈ Icc a b, closedBall (z t) r ⊆ C)
    (hcont : ContinuousOn (Function.uncurry (fun t => F t p)) (univ ×ˢ U))
    (hlocal : ∀ t : ℝ, ∀ v ∈ U, ∃ (R d : ℝ) (L : ℝ≥0), 0 < R ∧ 0 < d ∧
      ∀ s ∈ Icc (t - d) (t + d), LipschitzOnWith L (F s p) (closedBall v R))
    (hK : ∀ t ∈ Icc a b, LipschitzOnWith K (F t p) U)
    (hz : IsIntegralCurveOn z (fun t => F t q) (Icc a b))
    (herror : ∀ t ∈ Icc a b, dist (F t q (z t)) (F t p (z t)) ≤ ε)
    (hε : 0 ≤ ε) (hinit : dist x (z a) ≤ δ)
    (hsmall : gronwallBound δ K ε (b - a) < r) :
    ∃ y : ℝ → E, y a = x ∧ IsIntegralCurveOn y (fun t => F t p) (Icc a b) ∧
      MapsTo y (Icc a b) C ∧
      ∀ t ∈ Icc a b, dist (y t) (z t) ≤ gronwallBound δ K ε (b - a) := by
  have hδ : 0 ≤ δ := dist_nonneg.trans hinit
  have hδB : δ ≤ gronwallBound δ K ε (b - a) := by
    have hm := gronwallBound_mono hδ hε K.coe_nonneg (sub_nonneg.mpr hab)
    simpa only [gronwallBound_x0] using hm
  have hr : 0 < r := (hδ.trans hδB).trans_lt hsmall
  have hzU : MapsTo z (Icc a b) U := fun t ht =>
    hCU (htube t ht (mem_closedBall_self hr.le))
  have hxU : x ∈ U := hCU (htube a ⟨le_rfl, hab⟩
    (mem_closedBall.mpr (hinit.trans (hδB.trans hsmall.le))))
  obtain ⟨D, y, hD, hcD, ha, hy₀, hy, hyU, hmax⟩ :=
    exists_maximal_solution hU hcont hlocal a x hxU
  have hcompare : ∀ t ∈ D ∩ Icc a b,
      dist (y t) (z t) ≤ gronwallBound δ K ε (b - a) := by
    intro t ht
    have hsub : Icc a t ⊆ D := hcD.out ha ht.1
    have hsub' : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2.2
    have hd := dist_le_gronwallBound_of_parameters
      (fun s hs => hK s (hsub' hs))
      (fun s hs => (hy s (hsub hs)).hasDerivWithinAt)
      (hz.mono hsub') (fun s hs => hyU (hsub hs)) (fun s hs => hzU (hsub' hs))
      (fun s hs => herror s (hsub' hs)) (by simpa only [hy₀] using hinit)
      t ⟨ht.2.1, le_rfl⟩
    exact hd.trans (gronwallBound_mono hδ hε K.coe_nonneg (sub_le_sub_right ht.2.2 a))
  have hbound : ∀ t ∈ D ∩ Icc a b, y t ∈ C := by
    intro t ht
    exact htube t ht.2 (mem_closedBall.mpr ((hcompare t ht).trans hsmall.le))
  have hIcc : Icc a b ⊆ D := Icc_subset_domain_of_maximal_of_mem_isCompact hab hU hC hCU
    hcont hlocal hD hcD ha hy hyU
    (fun D' w hD' hcD' ha' hw₀ hw hwU =>
      (hmax D' w hD' hcD' ha' (hw₀.trans hy₀) hw hwU).1) hbound
  exact ⟨y, hy₀, fun t ht => (hy t (hIcc ht)).hasDerivWithinAt,
    fun t ht => hbound t ⟨hIcc ht, ht⟩, fun t ht => hcompare t ⟨hIcc ht, ht⟩⟩

/-- Nearby parameters and initial values admit solutions on the whole reference
interval inside the same compact tube. The preserved radius and Lipschitz bound
are fixed before the nearby parameter; parameter dependence itself is only
continuous. This supplies the existence part of finite-time continuous dependence. -/
theorem eventually_exists_solution_of_reference [FiniteDimensional ℝ E]
    {P : Type*} [TopologicalSpace P] {F : ℝ → P → E → E}
    {S : Set P} {U C : Set E} {a b r : ℝ} {K : ℝ≥0}
    {p₀ : P} {z : ℝ → E} {x : P → E}
    (hab : a ≤ b) (hr : 0 < r) (hp₀ : p₀ ∈ S)
    (hU : IsOpen U) (hC : IsCompact C) (hCU : C ⊆ U)
    (htube : ∀ t ∈ Icc a b, closedBall (z t) r ⊆ C)
    (hF : ContinuousOn (fun w : ℝ × P × E => F w.1 w.2.1 w.2.2)
      (univ ×ˢ S ×ˢ U))
    (hlocal : ∀ p ∈ S, ∀ t : ℝ, ∀ v ∈ U, ∃ (R d : ℝ) (L : ℝ≥0), 0 < R ∧ 0 < d ∧
      ∀ s ∈ Icc (t - d) (t + d), LipschitzOnWith L (F s p) (closedBall v R))
    (hK : ∀ p ∈ S, ∀ t ∈ Icc a b, LipschitzOnWith K (F t p) U)
    (hz : IsIntegralCurveOn z (fun t => F t p₀) (Icc a b))
    (hx : ContinuousWithinAt x S p₀) (hx₀ : x p₀ = z a) :
    ∀ᶠ p in 𝓝[S] p₀, ∃ y : ℝ → E, y a = x p ∧
      IsIntegralCurveOn y (fun t => F t p) (Icc a b) ∧ MapsTo y (Icc a b) C ∧
      ∀ t ∈ Icc a b, dist (y t) (z t) < r := by
  have hc : ContinuousAt (fun η : ℝ => gronwallBound η K η (b - a)) 0 := by
    unfold gronwallBound
    split_ifs <;> fun_prop
  have hs₀ : gronwallBound 0 K 0 (b - a) = 0 := gronwallBound_ε0_δ0 _ _
  have hs : ∀ᶠ η : ℝ in 𝓝 0, gronwallBound η K η (b - a) < r :=
    hc.preimage_mem_nhds (Iio_mem_nhds (by simpa only [hs₀] using hr))
  obtain ⟨d, hd, hsd⟩ := Metric.eventually_nhds_iff_ball.mp hs
  let η := d / 2
  have hη : 0 < η := half_pos hd
  have hηs : gronwallBound η K η (b - a) < r :=
    hsd η (by simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hη]
      using (show η < d from half_lt_self hd))
  have hzU : MapsTo z (Icc a b) U := fun t ht =>
    hCU (htube t ht (mem_closedBall_self hr.le))
  have hfc : ContinuousOn (fun w : P × ℝ => F w.2 w.1 (z w.2)) (S ×ˢ Icc a b) :=
    hF.comp (continuousOn_snd.prodMk (continuousOn_fst.prodMk
      (hz.continuousOn.comp continuousOn_snd (fun _ hw => hw.2))))
      (fun _ hw => ⟨trivial, hw.1, hzU hw.2⟩)
  obtain ⟨V, hV, hFV⟩ := isCompact_Icc.mem_uniformity_of_prod
    (f := fun p t => F t p (z t)) hfc hp₀ (Metric.dist_mem_uniformity hη)
  have hxi : ∀ᶠ p in 𝓝[S] p₀, dist (x p) (z a) < η := by
    rw [← hx₀]
    exact hx.preimage_mem_nhdsWithin (ball_mem_nhds _ hη)
  filter_upwards [hV, hxi, self_mem_nhdsWithin] with p hpV hxp hp
  have hcp : ContinuousOn (Function.uncurry (fun t => F t p)) (univ ×ˢ U) :=
    hF.comp (continuousOn_fst.prodMk (continuousOn_const.prodMk continuousOn_snd))
      (fun _ hw => ⟨trivial, hp, hw.2⟩)
  have herr : ∀ t ∈ Icc a b, dist (F t p₀ (z t)) (F t p (z t)) ≤ η := by
    intro t ht
    have hh : dist (F t p (z t)) (F t p₀ (z t)) < η := hFV p hpV t ht
    simpa only [dist_comm] using hh.le
  obtain ⟨y, hy₀, hy, hyC, hyd⟩ := exists_solution_on_Icc_of_reference hab hU hC hCU htube
    hcp (hlocal p hp) (hK p hp) hz herr hη.le hxp.le hηs
  exact ⟨y, hy₀, hy, hyC, fun t ht => (hyd t ht).trans_lt hηs⟩

/-- Finite-time stability of existence under the qualitative hypotheses: joint
continuity and state Lipschitz bounds locally uniform in time and parameter on
an open state domain. Every prescribed tolerance is preserved on the whole
reference interval for all sufficiently nearby parameters and initial values.
The neighborhood depends only on the field, compact parameter set, reference
trajectory, initial-value map, interval and tolerance. -/
theorem eventually_exists_solution_of_locally_lipschitz [FiniteDimensional ℝ E]
    {P : Type*} [TopologicalSpace P] {F : ℝ → P → E → E}
    {S : Set P} {U : Set E} {a b : ℝ} {p₀ : P} {z : ℝ → E} {x : P → E}
    (hab : a ≤ b) (hp₀ : p₀ ∈ S) (hS : IsCompact S) (hU : IsOpen U)
    (hF : ContinuousOn (fun w : ℝ × P × E => F w.1 w.2.1 w.2.2) (univ ×ˢ S ×ˢ U))
    (hlocal : ∀ t : ℝ, ∀ p ∈ S, ∀ v ∈ U,
      ∃ (V : Set P) (R d : ℝ) (L : ℝ≥0), IsOpen V ∧ p ∈ V ∧ 0 < R ∧ 0 < d ∧
        ∀ q ∈ S ∩ V, ∀ s ∈ Icc (t - d) (t + d),
          LipschitzOnWith L (F s q) (closedBall v R))
    (hz : IsIntegralCurveOn z (fun t => F t p₀) (Icc a b)) (hzU : MapsTo z (Icc a b) U)
    (hx : ContinuousWithinAt x S p₀) (hx₀ : x p₀ = z a) :
    ∀ ε > 0, ∀ᶠ p in 𝓝[S] p₀, ∃ y : ℝ → E, y a = x p ∧
      IsIntegralCurveOn y (fun t => F t p) (Icc a b) ∧ MapsTo y (Icc a b) U ∧
      ∀ t ∈ Icc a b, dist (y t) (z t) < ε := by
  intro ε hε
  let A := z '' Icc a b
  have hA : IsCompact A := isCompact_Icc.image_of_continuousOn hz.continuousOn
  obtain ⟨R, hR, hRU⟩ := hA.exists_cthickening_subset_open hU (image_subset_iff.mpr hzU)
  let C := cthickening (R / 4) A
  let V := thickening (R / 2) A
  have hCV : C ⊆ V := cthickening_subset_thickening' (by positivity) (by linarith) A
  have hVU : V ⊆ U :=
    (thickening_subset_cthickening (R / 2) A).trans
      ((cthickening_mono (by linarith : R / 2 ≤ R) A).trans hRU)
  obtain ⟨K, hK⟩ := exists_uniform_lipschitzOnWith_of_isCompact hS hA.cthickening hRU hF
    (fun t _ p hp v hv => hlocal t p hp v (hRU hv))
  have hKV : ∀ p ∈ S, ∀ t ∈ Icc a b, LipschitzOnWith K (F t p) V :=
    fun p hp t ht => (hK p hp t ht).mono
      ((thickening_subset_cthickening (R / 2) A).trans (cthickening_mono (by linarith) A))
  let r := min ε (R / 4)
  have hr : 0 < r := lt_min hε (by positivity)
  have htube : ∀ t ∈ Icc a b, closedBall (z t) r ⊆ C := by
    intro t ht
    exact (closedBall_subset_closedBall (min_le_right _ _)).trans
      (closedBall_subset_cthickening (mem_image_of_mem z ht) (R / 4))
  have hFV : ContinuousOn (fun w : ℝ × P × E => F w.1 w.2.1 w.2.2) (univ ×ˢ S ×ˢ V) :=
    hF.mono (prod_mono Subset.rfl (prod_mono Subset.rfl hVU))
  have hlV : ∀ p ∈ S, ∀ t : ℝ, ∀ v ∈ V, ∃ (d₁ d₂ : ℝ) (L : ℝ≥0),
      0 < d₁ ∧ 0 < d₂ ∧ ∀ s ∈ Icc (t - d₂) (t + d₂),
        LipschitzOnWith L (F s p) (closedBall v d₁) := by
    intro p hp t v hv
    obtain ⟨O, d₁, d₂, L, _, hpO, hd₁, hd₂, hL⟩ := hlocal t p hp v (hVU hv)
    exact ⟨d₁, d₂, L, hd₁, hd₂, hL p ⟨hp, hpO⟩⟩
  have he := eventually_exists_solution_of_reference hab hr hp₀ isOpen_thickening
    (hA.cthickening : IsCompact C) hCV htube hFV hlV hKV hz hx hx₀
  filter_upwards [he] with p hp
  obtain ⟨y, hy₀, hy, hyC, hyd⟩ := hp
  exact ⟨y, hy₀, hy, fun t ht => hVU (hCV (hyC ht)),
    fun t ht => (hyd t ht).trans_le (min_le_left _ _)⟩

/-- Joint continuous dependence on all data under the qualitative local
Lipschitz hypotheses. The parameter may be a product of the physical parameter
and initial state; only continuity of the initial-value map is assumed.
The state Lipschitz constant is obtained from compactness, not an extra premise. -/
theorem continuousOn_solution_of_locally_lipschitz
    {P : Type*} [TopologicalSpace P] {F : ℝ → P → E → E}
    {S : Set P} {U C : Set E} {a b : ℝ} {y : P → ℝ → E}
    (hab : a ≤ b) (hS : IsCompact S) (hC : IsCompact C) (hCU : C ⊆ U)
    (hF : ContinuousOn (fun w : ℝ × P × E => F w.1 w.2.1 w.2.2) (univ ×ˢ S ×ˢ U))
    (hlocal : ∀ t ∈ Icc a b, ∀ p ∈ S, ∀ v ∈ C,
      ∃ (V : Set P) (R d : ℝ) (L : ℝ≥0), IsOpen V ∧ p ∈ V ∧ 0 < R ∧ 0 < d ∧
        ∀ q ∈ S ∩ V, ∀ s ∈ Icc (t - d) (t + d),
          LipschitzOnWith L (F s q) (closedBall v R))
    (hsol : ∀ p ∈ S, IsIntegralCurveOn (y p) (fun t => F t p) (Icc a b))
    (hmem : ∀ p ∈ S, MapsTo (y p) (Icc a b) C)
    (hinit : ContinuousOn (fun p => y p a) S) :
    ContinuousOn (fun w : P × ℝ => y w.1 w.2) (S ×ˢ Icc a b) := by
  obtain ⟨K, hK⟩ := exists_uniform_lipschitzOnWith_of_isCompact hS hC hCU hF hlocal
  have hc : ContinuousOn (fun w : P × (ℝ × E) => F w.2.1 w.1 w.2.2)
      (S ×ˢ (Icc a b ×ˢ C)) :=
    hF.comp (continuousOn_snd.fst.prodMk (continuousOn_fst.prodMk continuousOn_snd.snd))
      (fun _ hw => ⟨trivial, hw.1, hCU hw.2.2⟩)
  exact continuousOn_solution_of_continuousOn hab hC hc
    (fun p hp => ⟨K, hK p hp⟩) hsol hmem hinit

omit [NormedSpace ℝ E] in
/-- A continuous initial-time shift preserves locally uniform state Lipschitz
bounds. The original local constants are shrunk in time and parameter; no
positive lower bound for the initial time is required. -/
theorem locally_lipschitz_time_translate
    {P : Type*} [TopologicalSpace P] {F : ℝ → P → E → E} {S : Set P} {U : Set E}
    {τ : P → ℝ} (hτ : ContinuousOn τ S)
    (hlocal : ∀ t : ℝ, ∀ p ∈ S, ∀ v ∈ U,
      ∃ (V : Set P) (R d : ℝ) (L : ℝ≥0), IsOpen V ∧ p ∈ V ∧ 0 < R ∧ 0 < d ∧
        ∀ q ∈ S ∩ V, ∀ s ∈ Icc (t - d) (t + d),
          LipschitzOnWith L (F s q) (closedBall v R)) :
    ∀ t : ℝ, ∀ p ∈ S, ∀ v ∈ U,
      ∃ (V : Set P) (R d : ℝ) (L : ℝ≥0), IsOpen V ∧ p ∈ V ∧ 0 < R ∧ 0 < d ∧
        ∀ q ∈ S ∩ V, ∀ s ∈ Icc (t - d) (t + d),
          LipschitzOnWith L (F (τ q + s) q) (closedBall v R) := by
  intro t p hp v hv
  obtain ⟨O, R, d, L, hO, hpO, hR, hd, hL⟩ := hlocal (τ p + t) p hp v hv
  have he : {q | τ q ∈ Ioo (τ p - d / 2) (τ p + d / 2)} ∈ 𝓝[S] p :=
    (hτ p hp).preimage_mem_nhdsWithin (Ioo_mem_nhds (by linarith) (by linarith))
  obtain ⟨W, hW, hpW, hτW⟩ := mem_nhdsWithin.mp he
  refine ⟨O ∩ W, R, d / 4, L, hO.inter hW, ⟨hpO, hpW⟩, hR, by positivity, ?_⟩
  intro q hq s hs
  have hqτ := hτW ⟨hq.2.2, hq.1⟩
  exact hL q ⟨hq.1, hq.2.1⟩ (τ q + s)
    ⟨by linarith [hqτ.1, hs.1], by linarith [hqτ.2, hs.2]⟩

/-- Continuous endpoint data for a compact family with variable initial time,
under the original qualitative state Lipschitz hypotheses. This covers the
initial time `x₀ = L⁻¹` continuously down to zero. Both physical and initial-value
parameters can be included in `P`. The elapsed endpoint `σ` also varies. -/
theorem continuousOn_endpoint_of_locally_lipschitz
    {P : Type*} [TopologicalSpace P] {F : ℝ → P → E → E}
    {S : Set P} {U C : Set E} {a b : ℝ} {y : P → ℝ → E} {τ σ : P → ℝ}
    (hab : a ≤ b) (hS : IsCompact S) (hC : IsCompact C) (hCU : C ⊆ U)
    (hτ : ContinuousOn τ S) (hσ : ContinuousOn σ S) (hσmem : MapsTo σ S (Icc a b))
    (hF : ContinuousOn (fun w : ℝ × P × E => F w.1 w.2.1 w.2.2) (univ ×ˢ S ×ˢ U))
    (hlocal : ∀ t : ℝ, ∀ p ∈ S, ∀ v ∈ U,
      ∃ (V : Set P) (R d : ℝ) (L : ℝ≥0), IsOpen V ∧ p ∈ V ∧ 0 < R ∧ 0 < d ∧
        ∀ q ∈ S ∩ V, ∀ s ∈ Icc (t - d) (t + d),
          LipschitzOnWith L (F s q) (closedBall v R))
    (hsol : ∀ p ∈ S, IsIntegralCurveOn (y p) (fun t => F t p)
      (Icc (τ p + a) (τ p + b)))
    (hmem : ∀ p ∈ S, MapsTo (y p) (Icc (τ p + a) (τ p + b)) C)
    (hinit : ContinuousOn (fun p => y p (τ p + a)) S) :
    ContinuousOn (fun p => y p (τ p + σ p)) S := by
  have hl := locally_lipschitz_time_translate hτ hlocal
  have hs : ∀ p ∈ S, IsIntegralCurveOn (fun s => y p (τ p + s))
      (fun s x => F (τ p + s) p x) (Icc a b) :=
    fun p hp => solution_time_translate (hsol p hp)
  have hm : ∀ p ∈ S, MapsTo (fun s => y p (τ p + s)) (Icc a b) C := by
    intro p hp s hs
    exact hmem p hp ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hj := continuousOn_solution_of_locally_lipschitz hab hS hC hCU
    (continuousOn_time_translate hτ hF) (fun t _ p hp v hv => hl t p hp v (hCU hv)) hs hm hinit
  exact hj.comp (continuousOn_id.prodMk hσ) (fun p hp => ⟨hp, hσmem hp⟩)

end EmcsfAcExtension.ODE
