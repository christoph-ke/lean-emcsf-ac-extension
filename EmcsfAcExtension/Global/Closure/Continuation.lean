module

public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Instances.Real.Lemmas
public import EmcsfAcExtension.Global.Defs.Original
public import EmcsfAcExtension.Global.Defs.Curves
public import EmcsfAcExtension.Global.Defs.Stages
public import EmcsfAcExtension.Frozen.PositiveExpIntegrand
public import EmcsfAcExtension.Frozen.SignedExpIntegrand
import EmcsfAcExtension.Global.Api.Domains
import EmcsfAcExtension.Global.Calculus.Sections
import EmcsfAcExtension.Local.Calculus.Sections
import EmcsfAcExtension.Local.Calculus.Reconstruction
import EmcsfAcExtension.Local.Api.Mono
import EmcsfAcExtension.Infra.Level.Graph
import EmcsfAcExtension.Global.Exterior.OpticsFrontier
import EmcsfAcExtension.Global.Exterior.Charge
import EmcsfAcExtension.Global.Terminal.OpticalUpper
import EmcsfAcExtension.Global.Observation.CylinderClock
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-! # Finite stopping and positive-radius continuation

The topological step uses strict improvements as inputs and never infers
an improvement from stage existence. The stop functions to which it applies
are cumulative extrema on one proper available finite path.
Geometric caps retain the actual clock without assuming schedule completion.
Source: `charged_SF_new_version.tex:L4104–L4106`.
-/

public section

open Set Filter Topology

namespace EmcsfAcExtension.Global.Closure

/-- [internal]
On a nonempty compact set, continuity identifies both weak and strict
pointwise bounds with bounds on the attained extrema. Nonemptiness is
explicit, so the same characterization applies to a singleton entry row.
There are no estimate constants. -/
theorem compact_extrema_bounds {α : Type*} [TopologicalSpace α]
    {K : Set α} (hK : IsCompact K) (hne : K.Nonempty) {f : α → ℝ}
    (hf : ContinuousOn f K) (c : ℝ) :
    (sSup (f '' K) ≤ c ↔ ∀ x ∈ K, f x ≤ c) ∧
      (sSup (f '' K) < c ↔ ∀ x ∈ K, f x < c) ∧
      (c ≤ sInf (f '' K) ↔ ∀ x ∈ K, c ≤ f x) ∧
      (c < sInf (f '' K) ↔ ∀ x ∈ K, c < f x) := by
  obtain ⟨x, hx, hmax, hxmax⟩ := hK.exists_sSup_image_eq_and_ge hne hf
  obtain ⟨y, hy, hmin, hymin⟩ := hK.exists_sInf_image_eq_and_le hne hf
  rw [hmax, hmin]
  exact ⟨⟨fun h z hz => (hxmax z hz).trans h, fun h => h x hx⟩,
    ⟨fun h z hz => (hxmax z hz).trans_lt h, fun h => h x hx⟩,
    ⟨fun h z hz => h.trans (hymin z hz), fun h => h y hy⟩,
    ⟨fun h z hz => h.trans_le (hymin z hz), fun h => h y hy⟩⟩

/-- [internal]
No continuous scalar stop can first reach its weak threshold when every
weakly stopped prefix has a strict improvement. The function is the maximum
of the normalized cumulative field and integral stops in the consumer.
This lemma controls an available path; local positive-radius continuation
must separately provide extension of that path. -/
theorem no_first_failure_of_estimates {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hentry : f a < 0)
    (himprove : ∀ t ∈ Icc a b, f t ≤ 0 → f t < 0) :
    ∀ t ∈ Icc a b, f t < 0 := by
  intro t ht
  by_contra hn
  have hft : 0 ≤ f t := le_of_not_gt hn
  obtain ⟨s, hs, hfs⟩ := intermediate_value_Icc ht.1
    (hf.mono (Icc_subset_Icc le_rfl ht.2)) ⟨hentry.le, hft⟩
  have hh := himprove s ⟨hs.1, hs.2.trans ht.2⟩ (hfs.le)
  rw [hfs] at hh
  exact lt_irrefl _ hh

/-- [internal]
The maximum of finitely many continuous stop functions encodes all weak
and strict inequalities at once, without selecting a first failure index. -/
theorem finite_stops_of_estimates {n : ℕ} {f : Fin (n + 1) → ℝ → ℝ} {a b : ℝ}
    (hf : ∀ i, ContinuousOn (f i) (Icc a b))
    (hentry : ∀ i, f i a < 0)
    (himprove : ∀ t ∈ Icc a b,
      (∀ i, f i t ≤ 0) → ∀ i, f i t < 0) :
    ∀ t ∈ Icc a b, ∀ i, f i t < 0 := by
  classical
  let F : ℝ → ℝ := fun t => (Finset.univ.image (fun i => f i t)).max'
    (Finset.univ_nonempty.image _)
  have hFval (t : ℝ) : ∃ i, F t = f i t := by
    have hh := Finset.max'_mem (Finset.univ.image (fun i => f i t))
      (Finset.univ_nonempty.image _)
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hh
    exact ⟨i, hi.symm⟩
  have hle (i : Fin (n + 1)) (t : ℝ) : f i t ≤ F t := by
    exact Finset.le_max' (Finset.univ.image (fun j => f j t)) (f i t)
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  have hFc : ContinuousOn F (Icc a b) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    let g : Icc a b → Fin (n + 1) → ℝ := fun t i => f i t
    have hg : Continuous (Function.uncurry g) := continuous_prod_of_discrete_right.mpr
      (fun i => continuousOn_iff_continuous_domRestrict.mp (hf i))
    have hc := isCompact_univ.continuous_sSup (f := g) hg
    apply hc.congr
    intro t
    apply le_antisymm
    · apply csSup_le (show (g t '' univ).Nonempty from ⟨g t 0, 0, mem_univ _, rfl⟩)
      rintro y ⟨i, _, rfl⟩
      exact hle i t
    · obtain ⟨i, hi⟩ := hFval t
      change F t ≤ sSup (g t '' univ)
      rw [hi]
      exact le_csSup (Set.toFinite (g t '' univ)).bddAbove ⟨i, mem_univ _, rfl⟩
  have hFa : F a < 0 := by obtain ⟨i, hi⟩ := hFval a; rw [hi]; exact hentry i
  have hFimp (t : ℝ) (ht : t ∈ Icc a b) (hFt : F t ≤ 0) : F t < 0 := by
    obtain ⟨i, hi⟩ := hFval t
    rw [hi]
    exact himprove t ht (fun j => (hle j t).trans hFt) i
  intro t ht i
  exact (hle i t).trans_lt (no_first_failure_of_estimates hFc hFa hFimp t ht)

/-- [internal]
The radius is C¹ with its exact null differential at every strictly
interior off-axis original point. Both partials follow from the frozen
integral equations. No smoothness of a scalar derivative is used. -/
theorem radius_differential_at {ui e u v : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hiu : ui < u) (huv : u < v) (hv : v < 0) :
    ContDiffAt ℝ 1 (Function.uncurry S.r) (u, v) ∧
      HasFDerivAt (Function.uncurry S.r)
        (S.nu u v • ContinuousLinearMap.fst ℝ ℝ ℝ +
          S.lam u v • ContinuousLinearMap.snd ℝ ℝ ℝ) (u, v) := by
  let w := v / 2
  have hvw : v < w := by dsimp [w]; linarith only [hv]
  have hw : w < 0 := by dsimp [w]; linarith only [hv]
  have hiw : ui < w := hiu.trans (huv.trans hvw)
  have htri : triangle ui w ⊆ origDomain ui := triangle_subset_origDomain le_rfl hw
  have hST := Local.isSolution_mono h.solution htri
  have hct := Local.IsSolution.contDiffOn_r hST hiw
  have hopen : IsOpen {p : ℝ × ℝ | ui < p.1 ∧ p.1 < p.2 ∧ p.2 < w} :=
    (isOpen_lt continuous_const continuous_fst).inter
      ((isOpen_lt continuous_fst continuous_snd).inter (isOpen_lt continuous_snd continuous_const))
  have hnhds : triangle ui w ∈ 𝓝 (u, v) :=
    mem_of_superset (hopen.mem_nhds ⟨hiu, huv, hvw⟩)
      (fun p hp => ⟨hp.1.le, hp.2.1.le, hp.2.2.le⟩)
  have hc : ContDiffAt ℝ 1 (Function.uncurry S.r) (u, v) :=
    (hct (u, v) ⟨hiu.le, huv.le, hvw.le⟩).contDiffAt hnhds
  have hTotal : HasFDerivAt (Function.uncurry S.r)
      (fderiv ℝ (Function.uncurry S.r) (u, v)) (u, v) :=
    (hc.differentiableAt (by norm_num)).hasFDerivAt
  have hinseg : inSeg ui v v ⊆ origDomain ui := by
    rintro ⟨x, y⟩ ⟨hx, hxv, rfl⟩
    exact ⟨hx, hxv.trans_lt hv, hxv, hv.le⟩
  have hnu : HasDerivAt (fun x => S.r x v) (S.nu u v) u := by
    apply Local.hasDerivAt_of_integralForm_interior ⟨hiu, huv⟩
      ((Calculus.continuousOn_in_section h.solution.cont_nu hinseg).mono Ioo_subset_Icc_self)
    intro c d hc₀ hcd₀ hd₀
    exact (h.solution.eq_in c d v hcd₀ hd₀ (by
      rintro ⟨x, y⟩ ⟨hcx, hxd, rfl⟩
      exact ⟨hc₀.le.trans hcx, (hxd.trans_lt hd₀).trans hv, hxd.trans hd₀.le, hv.le⟩)).1
  have houtseg : outSeg u u w ⊆ origDomain ui := by
    rintro ⟨x, y⟩ ⟨rfl, hy⟩
    exact ⟨hiu.le, huv.trans (hvw.trans hw), hy.1, hy.2.trans hw.le⟩
  have hlam := Local.IsSolution.hasDerivAt_radius_out h.solution houtseg ⟨huv, hvw⟩
  let L := fderiv ℝ (Function.uncurry S.r) (u, v)
  have hLnu : L (1, 0) = S.nu u v := by
    have hpath : HasDerivAt (fun x : ℝ => (x, v)) (1, 0) u :=
      (hasDerivAt_id u).prodMk (hasDerivAt_const u v)
    have hh : HasDerivAt (fun x => S.r x v) (L (1, 0)) u :=
      HasFDerivAt.comp_hasDerivAt (l := Function.uncurry S.r) (l' := L)
        (f := fun x : ℝ => (x, v)) u hTotal hpath
    exact hh.unique hnu
  have hLlam : L (0, 1) = S.lam u v := by
    have hpath : HasDerivAt (fun x : ℝ => (u, x)) (0, 1) v :=
      (hasDerivAt_const v u).prodMk (hasDerivAt_id v)
    have hh : HasDerivAt (fun x => S.r u x) (L (0, 1)) v :=
      HasFDerivAt.comp_hasDerivAt (l := Function.uncurry S.r) (l' := L)
        (f := fun x : ℝ => (u, x)) v hTotal hpath
    exact hh.unique hlam
  have hL : L = S.nu u v • ContinuousLinearMap.fst ℝ ℝ ℝ +
      S.lam u v • ContinuousLinearMap.snd ℝ ℝ ℝ := by
    apply ContinuousLinearMap.ext
    rintro ⟨x, y⟩
    have hp : (x, y) = x • ((1, 0) : ℝ × ℝ) + y • ((0, 1) : ℝ × ℝ) := by
      ext <;> simp
    calc
      L (x, y) = L (x • ((1, 0) : ℝ × ℝ) + y • ((0, 1) : ℝ × ℝ)) := congrArg L hp
      _ = x * S.nu u v + y * S.lam u v := by rw [map_add, map_smul, map_smul, hLnu, hLlam]; rfl
      _ = _ := by simp; ring
  refine ⟨hc, ?_⟩
  change HasFDerivAt (Function.uncurry S.r) L (u, v) at hTotal
  simpa only [hL] using hTotal

/-- [internal]
Local continuation of the same positive-radius level curve at every proper
interior original point. This is a parametrization of the existing
solution. It supplies the local geometric step needed after the strict
stops have excluded a first failure; it asserts no scheduled stage length.
There are no constants or observation premises. -/
theorem positive_radius_local_continuation {ui e u v : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hiu : ui < u) (huv : u < v) (hv : v < 0) :
    ∃ g : ℝ → ℝ, g u = v ∧ ContDiffAt ℝ 1 g u ∧
      HasDerivAt g (-S.nu u v / S.lam u v) u ∧
      (∀ᶠ x in 𝓝 u, ui < x ∧ x < g x ∧ g x < 0 ∧ S.r x (g x) = S.r u v) := by
  have hp : (u, v) ∈ origDomain ui := ⟨hiu.le, huv.trans hv, huv.le, hv.le⟩
  obtain ⟨hc, hd⟩ := radius_differential_at h hiu huv hv
  have hopen : IsOpen {p : ℝ × ℝ | ui < p.1 ∧ p.1 < p.2 ∧ p.2 < 0} :=
    (isOpen_lt continuous_const continuous_fst).inter
      ((isOpen_lt continuous_fst continuous_snd).inter (isOpen_lt continuous_snd continuous_const))
  obtain ⟨g, hg, hgc, hgd, hlevel⟩ := Level.exists_levelGraph_in_open hopen
    (show (u, v) ∈ {p : ℝ × ℝ | ui < p.1 ∧ p.1 < p.2 ∧ p.2 < 0} from ⟨hiu, huv, hv⟩)
    hc hd (h.solution.lam_pos _ hp).ne'
  refine ⟨g, hg, hgc, hgd, ?_⟩
  filter_upwards [hlevel] with x hx
  exact ⟨hx.1.1, hx.1.2.1, hx.1.2.2, hx.2⟩

/-- [internal]
A fixed positive radius below every terminal radius has one C¹ increasing
graph over the whole proper closed incoming interval. The exact speed
holds also as a within derivative at both endpoints. Local implicit graphs
agree with the unique outgoing root, so no stage existence is assumed.
There are no estimate constants. Source: charged_SF_new_version.tex:L4104–L4106. -/
theorem positive_radius_level_graph {ui e a b R : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hia : ui < a) (_hab : a ≤ b) (hb : b < 0)
    (hR : 0 < R) (hupper : ∀ u ∈ Icc a b, R < S.r u 0) :
    ∃ V : ℝ → ℝ, ContDiffOn ℝ 1 V (Icc a b) ∧ StrictMonoOn V (Icc a b) ∧
      (∀ u ∈ Icc a b, u < V u ∧ V u < 0 ∧ S.r u (V u) = R) ∧
      ∀ u ∈ Icc a b,
        HasDerivWithinAt V (-S.nu u (V u) / S.lam u (V u)) (Icc a b) u := by
  have hroot (u : ℝ) (hu : u ∈ Icc a b) :
      ∃ v, u < v ∧ v < 0 ∧ S.r u v = R := by
    have hu0 := hu.2.trans_lt hb
    have hs : outSeg u u 0 ⊆ origDomain ui := by
      rintro ⟨x, v⟩ ⟨rfl, hv⟩
      exact ⟨hia.le.trans hu.1, hu0, hv⟩
    have haxis := (h.solution.axis u (hs ⟨rfl, le_rfl, hu0.le⟩)).1
    obtain ⟨v, hv, hvr⟩ := Exterior.exists_outgoing_radius_between h hu0.le hs
      (by rw [haxis]; exact hR.le) (hupper u hu).le
    have huv : u < v := by
      apply lt_of_le_of_ne hv.1
      intro heq
      rw [← heq, haxis] at hvr
      exact hR.ne hvr
    have hv0 : v < 0 := by
      apply lt_of_le_of_ne hv.2
      intro heq
      rw [heq] at hvr
      exact (hupper u hu).ne hvr.symm
    exact ⟨v, huv, hv0, hvr⟩
  choose W hW using hroot
  let V := fun u => if hu : u ∈ Icc a b then W u hu else 0
  have hV (u : ℝ) (hu : u ∈ Icc a b) :
      u < V u ∧ V u < 0 ∧ S.r u (V u) = R := by
    simpa only [V, dite_eq_left hu] using hW u hu
  have hlocal (u : ℝ) (hu : u ∈ Icc a b) :
      ContDiffWithinAt ℝ 1 V (Icc a b) u ∧
      HasDerivWithinAt V (-S.nu u (V u) / S.lam u (V u)) (Icc a b) u := by
    obtain ⟨g, hgu, hgc, hgd, hlevel⟩ := positive_radius_local_continuation h
      (hia.trans_le hu.1) (hV u hu).1 (hV u hu).2.1
    have heq : V =ᶠ[𝓝[Icc a b] u] g := by
      filter_upwards [hlevel.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hx hxm
      have hvx := hV x hxm
      apply (Exterior.outgoing_radius_strictMono h
        ⟨hia.le.trans hxm.1, hxm.2.trans_lt hb⟩).injOn
        ⟨hvx.1.le, hvx.2.1.le⟩ ⟨hx.2.1.le, hx.2.2.1.le⟩
      exact hvx.2.2.trans ((hV u hu).2.2.symm.trans hx.2.2.2.symm)
    exact ⟨hgc.contDiffWithinAt.congr_of_eventuallyEq heq hgu.symm,
      hgd.hasDerivWithinAt.congr_of_eventuallyEq heq hgu.symm⟩
  have hc : ContDiffOn ℝ 1 V (Icc a b) := fun u hu => (hlocal u hu).1
  refine ⟨V, hc, ?_, hV, fun u hu => (hlocal u hu).2⟩
  apply strictMonoOn_of_deriv_pos (convex_Icc a b) hc.continuousOn
  intro u hu
  rw [interior_Icc] at hu
  have hu' := Ioo_subset_Icc_self hu
  rw [((hlocal u hu').2.hasDerivAt (Icc_mem_nhds hu.1 hu.2)).deriv]
  have hp : (u, V u) ∈ origDomain ui :=
    ⟨hia.le.trans hu'.1, hu'.2.trans_lt hb, (hV u hu').1.le, (hV u hu').2.1.le⟩
  exact div_pos (neg_pos.mpr (h.solution.nu_neg _ hp)) (h.solution.lam_pos _ hp)

/-- [internal]
The preceding global level graph admits the actual boundary clock on the
entire retained-radius interval. This gives a proper available cylinder
before selecting any prescribed schedule endpoint. Its duration is exactly
the existing clock, rather than a stage-existence hypothesis. Constants: none.
Source: charged_SF_new_version.tex:L4104–L4106. -/
theorem clock_cylinder_on_retained_region {ui e a b R : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hia : ui < a) (hab : a < b) (hb : b < 0)
    (hR : 0 < R) (hupper : ∀ u ∈ Icc a b, R < S.r u 0) :
    ∃ V : ℝ → ℝ, ∃ T > 0, T = cylinderClock S V a b ∧
      ∃ γ : ClockCylinder S (origDomain ui) R 0 T,
        γ.U 0 = a ∧ γ.U T = b ∧ γ.V 0 = V a ∧ γ.V T = V b ∧
        (∀ u ∈ Icc a b, u < V u ∧ V u < 0 ∧ S.r u (V u) = R) ∧
        ∀ τ ∈ Icc 0 T, γ.U τ ∈ Icc a b ∧ γ.V τ = V (γ.U τ) := by
  obtain ⟨V, hc, _, hr, hd⟩ := positive_radius_level_graph h hia hab.le hb hR hupper
  obtain ⟨T, hT, hclock, γ, hU₀, hUT, hV₀, hVT, hgraph⟩ :=
    Cylinder.exists_clockCylinder_of_levelGraph h.solution hab hc
      (fun u hu => ⟨hia.le.trans hu.1, hu.2.trans_lt hb, (hr u hu).1.le, (hr u hu).2.1.le⟩)
      (fun u hu => (hr u hu).2.2) hd
  exact ⟨V, T, hT, hclock, γ, hU₀, hUT, hV₀, hVT, hr, hgraph⟩

/-- [internal]
Before any stopping argument, a positive-radius cylinder can be followed
until either its prescribed clock endpoint or the proper terminal row of
radius `Rmin` is reached. The actual available clock is capped by the
prescribed duration. Neither duration is identified with the other.
The graph, its exact endpoint derivatives and its proper labels are retained
for finite append. There are no estimate constants.
Source: charged_SF_new_version.tex:L4104–L4106; approved internal project record. -/
theorem capped_clock_cylinder {ui e a v R Rmin T : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hia : ui < a) (hav : a < v) (hv : v < 0)
    (hR : 0 < R) (hRmin : R < Rmin) (hstart : S.r a v = R)
    (hterminal : Rmin < S.r a 0) (hT : 0 < T) :
    ∃ W : ℝ → ℝ, ∃ b ∈ Ioo a 0, ∃ t : ℝ, 0 < t ∧ t ≤ T ∧
      ∃ γ : ClockCylinder S (origDomain ui) R 0 t,
        γ.U 0 = a ∧ γ.V 0 = v ∧ W a = v ∧
        γ.U t ∈ Ioc a b ∧
        ContDiffOn ℝ 1 W (Icc a b) ∧ StrictMonoOn W (Icc a b) ∧
        (∀ u ∈ Icc a b, u < W u ∧ W u < 0 ∧ S.r u (W u) = R) ∧
        (∀ u ∈ Icc a b,
          HasDerivWithinAt W (-S.nu u (W u) / S.lam u (W u)) (Icc a b) u) ∧
        (∀ τ ∈ Icc 0 t, γ.U τ ∈ Icc a b ∧ γ.V τ = W (γ.U τ)) ∧
        (∀ u ∈ Icc a b, Rmin ≤ S.r u 0) ∧ S.r b 0 = Rmin ∧
        (t = T ∨ γ.U t = b) := by
  have ha0 : a < 0 := hav.trans hv
  have hsub : origDomain a ⊆ origDomain ui := fun p hp => ⟨hia.le.trans hp.1, hp.2⟩
  have himage := Terminal.terminal_radius_image_Ioo ha0
    (Local.isSolution_mono h.solution hsub) (fun p hp => h.mu p (hsub hp))
  have hRmin0 : 0 < Rmin := hR.trans hRmin
  have hmem : Rmin ∈ (fun u => S.r u 0) '' Ioo a 0 := by
    rw [himage]
    exact ⟨hRmin0, hterminal⟩
  obtain ⟨b, hb, hRb⟩ := hmem
  have hretained (u : ℝ) (hu : u ∈ Icc a b) : Rmin ≤ S.r u 0 := by
    rw [← hRb]
    exact (Terminal.terminal_radius_strictAntiOn h.solution).antitoneOn
      ⟨hia.le.trans hu.1, hu.2.trans_lt hb.2⟩ ⟨hia.le.trans hb.1.le, hb.2⟩ hu.2
  obtain ⟨W, hW, hWmono, hWr, hWrate⟩ := positive_radius_level_graph h hia hb.1.le hb.2 hR
    (fun u hu => hRmin.trans_le (hretained u hu))
  have hWa : W a = v := by
    apply (Exterior.outgoing_radius_strictMono h ⟨hia.le, ha0⟩).injOn
      ⟨(hWr a ⟨le_rfl, hb.1.le⟩).1.le, (hWr a ⟨le_rfl, hb.1.le⟩).2.1.le⟩
      ⟨hav.le, hv.le⟩
    exact (hWr a ⟨le_rfl, hb.1.le⟩).2.2.trans hstart.symm
  obtain ⟨Ta, hTa, _hclock, γ, hU₀, hUT, hV₀, _hVT, hgraph⟩ :=
    Cylinder.exists_clockCylinder_of_levelGraph h.solution hb.1 hW
      (fun u hu => ⟨hia.le.trans hu.1, hu.2.trans_lt hb.2,
        (hWr u hu).1.le, (hWr u hu).2.1.le⟩)
      (fun u hu => (hWr u hu).2.2) hWrate
  let t := min Ta T
  have ht : 0 < t := lt_min hTa hT
  have htTa : t ≤ Ta := min_le_left _ _
  have hinterval : Icc 0 t ⊆ Icc 0 Ta := Icc_subset_Icc le_rfl htTa
  let γ' : ClockCylinder S (origDomain ui) R 0 t :=
    { U := γ.U, V := γ.V
      c1_U := γ.c1_U.mono hinterval
      c1_V := γ.c1_V.mono hinterval
      mem := fun x hx => γ.mem x (hinterval hx)
      radius := fun x hx => γ.radius x (hinterval hx)
      rate_U := fun x hx => (γ.rate_U x (hinterval hx)).mono hinterval
      rate_V := fun x hx => (γ.rate_V x (hinterval hx)).mono hinterval }
  have hend : γ'.U t ∈ Ioc a b := by
    refine ⟨?_, (hgraph t ⟨ht.le, htTa⟩).1.2⟩
    change a < γ.U t
    rw [← hU₀]
    exact γ.strictMonoOn_U h.solution ⟨le_rfl, hTa.le⟩ ⟨ht.le, htTa⟩ ht
  refine ⟨W, b, hb, t, ht, min_le_right _ _, γ', hU₀,
    hV₀.trans hWa, hWa, hend, hW, hWmono, hWr, hWrate,
    (fun τ hτ => hgraph τ (hinterval hτ)), hretained, hRb, ?_⟩
  by_cases hshort : T ≤ Ta
  · exact Or.inl (min_eq_right hshort)
  · right
    change γ.U t = b
    simpa only [t, min_eq_left (le_of_not_ge hshort)] using hUT

/-- [internal]
A compatible family of finite boundary graphs has one common graph on
every visited prefix. Values outside the visited union use the entry label.
No regularity or stage-existence conclusion is assumed or inferred here;
`transportBoundary` transfers each produced finite geometric record.
There are no estimate constants. Source: charged_SF_new_version.tex:L4106–L4115. -/
theorem common_boundary_of_coherent_prefixes (a v₀ : ℝ) (U : ℕ → ℝ)
    (V : ℕ → ℝ → ℝ)
    (hcompat : ∀ M N, M ≤ N → EqOn (V N) (V M) (Icc a (U M))) :
    ∃ vb : ℝ → ℝ, ∀ N, EqOn vb (V N) (Icc a (U N)) := by
  classical
  let vb := fun u => if hu : ∃ N, u ∈ Icc a (U N) then V (Nat.find hu) u else v₀
  refine ⟨vb, ?_⟩
  intro N u hu
  have hex : ∃ M, u ∈ Icc a (U M) := ⟨N, hu⟩
  change (if hx : ∃ M, u ∈ Icc a (U M) then V (Nat.find hx) u else v₀) = V N u
  rw [dite_eq_left hex]
  rcases le_total (Nat.find hex) N with hm | hm
  · exact (hcompat (Nat.find hex) N hm (Nat.find_spec hex)).symm
  · exact hcompat N (Nat.find hex) hm hu

/-- [internal]
Every point between the first and last of a nonempty finite list of cuts
belongs to a successive cut interval. Degenerate intervals are included.
There are no estimate constants. -/
theorem stage_interval_cover {N : ℕ} (hN : 0 < N)
    (cuts : Fin (N + 1) → ℝ) {u : ℝ}
    (hu : u ∈ Icc (cuts 0) (cuts (Fin.last N))) :
    ∃ n : Fin N, u ∈ Icc (cuts n.castSucc) (cuts n.succ) := by
  induction N with
  | zero => omega
  | succ N ih =>
    by_cases hz : N = 0
    · subst N
      exact ⟨0, hu⟩
    · by_cases hle : u ≤ cuts (Fin.last N).castSucc
      · obtain ⟨n, hn⟩ := ih (by omega) (fun i => cuts i.castSucc) ⟨hu.1, hle⟩
        exact ⟨n.castSucc, by simpa only [Fin.castSucc_succ] using hn⟩
      · exact ⟨Fin.last N, (lt_of_not_ge hle).le, hu.2⟩

/-- [node sec:charged-closure#positive-radius-stage-continuation]
Every point of an available finite stage, including its connector, has a
proper positive-duration continuation of its radius cylinder. The retained
terminal radius and the prescribed upper radius exclude both terminal
edges; off-axis positivity excludes the axis. The proof first obtains an
actual local clock; it asserts no equality with a prescribed stage duration.
There are no estimate constants. Source: charged_SF_new_version.tex:L4107–L4111. -/
theorem positive_radius_stage_continuation {ui e a b v₀ ρ R₀ b₀ : ℝ} {S : Fields}
    (h : OriginalData ui e S) {vb : ℝ → ℝ} {N : ℕ}
    (B : FiniteBoundary S ui a b v₀ ρ vb N) (hN : 0 < N) (hia : ui < a)
    (hradii : ∀ n, B.radii n ≤ b₀) (hb₀ : b₀ < R₀ / 2)
    (hretained : ∀ u ∈ Icc a b, R₀ / 2 ≤ S.r u 0) :
    ∀ u ∈ Icc a b,
      ui < u ∧ u < vb u ∧ vb u < 0 ∧ 0 < S.r u (vb u) ∧
      ∃ T > 0, ∃ γ : ClockCylinder S (origDomain ui) (S.r u (vb u)) 0 T,
        γ.U 0 = u ∧ γ.V 0 = vb u ∧ ∀ τ ∈ Icc 0 T, γ.V τ < 0 := by
  have cR : ContinuousOn (fun u => S.r u 0) (Ioo ui 0) :=
    h.solution.cont_r.comp (continuousOn_id.prodMk continuousOn_const)
      (fun u hu => ⟨hu.1.le, hu.2, hu.2.le, le_rfl⟩)
  intro u hu
  have hp := B.mem u hu
  have hiu := hia.trans_le hu.1
  have hoff := B.off_axis u hu
  obtain ⟨n, hn⟩ := stage_interval_cover hN B.cuts
    (show u ∈ Icc (B.cuts 0) (B.cuts (Fin.last N)) by simpa only [B.first, B.last] using hu)
  have hRupper : S.r u (vb u) < S.r u 0 :=
    ((B.radius_range n u hn).2.trans (hradii n)).trans_lt (hb₀.trans_le (hretained u hu))
  have hv : vb u < 0 := lt_of_le_of_ne hp.2.2.2 (fun heq => by
    rw [heq] at hRupper
    exact (lt_irrefl _ hRupper))
  have hR := h.solution.r_pos (u, vb u) hp hoff
  have hloc : ∀ᶠ x in 𝓝 u, x ∈ Ioo ui 0 ∧ S.r u (vb u) < S.r x 0 := by
    filter_upwards [Ioo_mem_nhds hiu hp.2.1,
      ((cR.continuousAt (isOpen_Ioo.mem_nhds ⟨hiu, hp.2.1⟩)).tendsto).eventually
        (Ioi_mem_nhds hRupper)] with x hx hRx
    exact ⟨hx, hRx⟩
  obtain ⟨d, hd, hball⟩ := Metric.mem_nhds_iff.mp hloc
  let u' := u + d / 2
  have huu' : u < u' := by dsimp [u']; linarith only [hd]
  have hrange (x : ℝ) (hx : x ∈ Icc u u') :
      x ∈ Ioo ui 0 ∧ S.r u (vb u) < S.r x 0 := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hx.1)]
    dsimp only [u'] at hx
    linarith only [hx.2, hd]
  obtain ⟨W, T, hT, _, γ, hU₀, _hUT, hV₀, _hVT, hWr, hgraph⟩ :=
    clock_cylinder_on_retained_region h hiu huu' (hrange u' ⟨huu'.le, le_rfl⟩).1.2
      hR (fun x hx => (hrange x hx).2)
  have hWa : W u = vb u := by
    apply (Exterior.outgoing_radius_strictMono h ⟨hiu.le, hp.2.1⟩).injOn
      ⟨(hWr u ⟨le_rfl, huu'.le⟩).1.le, (hWr u ⟨le_rfl, huu'.le⟩).2.1.le⟩
      ⟨hoff.le, hv.le⟩
    exact (hWr u ⟨le_rfl, huu'.le⟩).2.2
  refine ⟨hiu, hoff, hv, hR, T, hT, γ, hU₀, hV₀.trans hWa, ?_⟩
  intro τ hτ
  rw [(hgraph τ hτ).2]
  exact (hWr _ (hgraph τ hτ).1).2.1

/-- [internal]
Cap an available incoming connector at its target endpoint or the first
proper terminal row of radius `Rmin`. Every retained point satisfies the
weak radius stop. Strict radius improvement can therefore exclude the
terminal-row alternative before completing that connector. This geometric
cap uses no field stopping or clock estimate. Constants: none.
Source: charged_SF_new_version.tex:L3905–L3907, L4107–L4107. -/
theorem terminal_radius_cap {ui e a b Rmin : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hia : ui ≤ a) (hab : a < b) (hb : b < 0)
    (hstart : Rmin < S.r a 0) :
    ∃ c ∈ Ioc a b, (∀ u ∈ Icc a c, Rmin ≤ S.r u 0) ∧
      (c = b ∨ S.r c 0 = Rmin) := by
  have hanti := (Terminal.terminal_radius_strictAntiOn h.solution).antitoneOn
  have hmono (c : ℝ) (hc : c ∈ Icc a b) (u : ℝ) (hu : u ∈ Icc a c) :
      S.r c 0 ≤ S.r u 0 :=
    hanti ⟨hia.trans hu.1, (hu.2.trans hc.2).trans_lt hb⟩
      ⟨hia.trans hc.1, hc.2.trans_lt hb⟩ hu.2
  by_cases hend : Rmin ≤ S.r b 0
  · exact ⟨b, ⟨hab, le_rfl⟩, fun u hu => hend.trans (hmono b ⟨hab.le, le_rfl⟩ u hu),
      Or.inl rfl⟩
  · have hc : ContinuousOn (fun u => S.r u 0) (Icc a b) :=
      h.solution.cont_r.comp (continuousOn_id.prodMk continuousOn_const)
        (fun u hu => ⟨hia.trans hu.1, hu.2.trans_lt hb, (hu.2.trans_lt hb).le, le_rfl⟩)
    obtain ⟨c, hc, hRc⟩ := intermediate_value_Icc' hab.le hc
      (show Rmin ∈ Icc (S.r b 0) (S.r a 0) from ⟨(lt_of_not_ge hend).le, hstart.le⟩)
    have hac : a < c := lt_of_le_of_ne hc.1 (by
      intro heq
      rw [← heq] at hRc
      exact hstart.ne' hRc)
    refine ⟨c, ⟨hac, hc.2⟩, ?_, Or.inr hRc⟩
    intro u hu
    rw [← hRc]
    exact hmono c hc u hu

/-- [internal]
On an incoming exterior history the late relative-charge inequality places
the signed exponent between zero and its positive majorant. This exact
pointwise statement has no estimate constant or regularity hypothesis. -/
theorem signed_exponent_bounds {S : Fields} {u v : ℝ}
    (hr : 0 < S.r u v) (hn : S.nu u v < 0) (hg : 0 < 1 - S.mu u v)
    (hq : S.Q u v ^ 2 / S.r u v ^ 2 ≤ S.mu u v) :
    0 ≤ signedExpIntegrand S u v ∧
      signedExpIntegrand S u v ≤ positiveExpIntegrand S u v := by
  constructor
  · exact div_nonneg (mul_nonneg (neg_pos.mpr hn).le (sub_nonneg.mpr hq))
      (mul_nonneg hg.le hr.le)
  · apply div_le_div_of_nonneg_right _ (mul_nonneg hg.le hr.le)
    exact mul_le_mul_of_nonneg_left (sub_le_self _
      (div_nonneg (sq_nonneg _) (sq_nonneg _))) (neg_pos.mpr hn).le

/-- [internal]
The outgoing optical comparison gives a uniform bound for the mixed
boundary-to-terminal clock ratio. The source optical estimate is supplied
by interaction with its boundary budget, rather than assumed of the
original solution. -/
theorem clock_ratio_of_estimates {n nt E : ℝ} (hn : n < 0) (hnt : nt < 0)
    (hlog : Real.log ((-nt) / (-n)) ≤ E) (hsmall : E < Real.log 2) :
    (-nt) / (-n) < 2 := by
  exact (Real.log_lt_log_iff (div_pos (neg_pos.mpr hnt) (neg_pos.mpr hn))
    (by norm_num)).mp (hlog.trans_lt hsmall)

end EmcsfAcExtension.Global.Closure
