module

public import EmcsfAcExtension.Global.Defs.Domains
public import EmcsfAcExtension.Global.Defs.Stages
public import EmcsfAcExtension.Global.Defs.Interaction
public import EmcsfAcExtension.Global.Defs.Original
public import EmcsfAcExtension.Global.Defs.Curves
public import EmcsfAcExtension.Infra.AC.Primitive
public import EmcsfAcExtension.Infra.AC.Variation
import EmcsfAcExtension.Global.Api.Domains
import EmcsfAcExtension.Global.Interaction.ClosuresFinite
import EmcsfAcExtension.Global.Renormalized.WeakTransfer
import EmcsfAcExtension.Global.Observation.Energy
import EmcsfAcExtension.Global.Observation.CylinderClock
import Mathlib.Topology.Order.Compact

/-! # Continuous finite cutoff functionals

The cumulative exterior is the exact `exteriorDomain`. Its earlier-time
projection preserves membership because the boundary label is nondecreasing.
Extrema therefore reduce to extrema over one fixed compact set. Rough
integral tails use absolute continuity of an L¹ primitive.
Source: `charged_SF_new_version.tex:L4104–L4105`, internal project record (C1)–(C2).
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Global.Closure

/-- [internal]
Boundary graphs agreeing on the visited incoming interval define exactly
the same stopped exterior, including every endpoint. This transports a
cutoff through restriction or append without changing any source history.
There are no estimate constants. -/
theorem exteriorDomain_congr_boundary {ui a b : ℝ} {vb vb' : ℝ → ℝ}
    (heq : EqOn vb' vb (Icc a b)) :
    exteriorDomain ui a b vb' = exteriorDomain ui a b vb := by
  ext p
  constructor
  · intro hp
    refine ⟨hp.1, hp.2.1, hp.2.2.1, ?_⟩
    rw [← heq ⟨hp.2.1, hp.2.2.1⟩]
    exact hp.2.2.2
  · intro hp
    refine ⟨hp.1, hp.2.1, hp.2.2.1, ?_⟩
    rw [heq ⟨hp.2.1, hp.2.2.1⟩]
    exact hp.2.2.2

/-- [internal]
A proper finite exterior is compact, including the initial row and every
visited boundary point. No field estimate is used to obtain compactness. -/
theorem isCompact_exteriorDomain {ui a b : ℝ} {vb : ℝ → ℝ}
    (hab : a ≤ b) (hia : ui ≤ a) (hb : b < 0)
    (hc : ContinuousOn vb (Icc a b)) (hm : MonotoneOn vb (Icc a b))
    (hproper : ∀ u ∈ Icc a b, u < vb u ∧ vb u ≤ 0) :
    IsCompact (exteriorDomain ui a b vb) := by
  let Γ : ℝ → ℝ := fun u => vb (max a (min b u))
  have hclamp (u : ℝ) : max a (min b u) ∈ Icc a b :=
    ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩
  have hΓ : Continuous Γ := hc.comp_continuous (by fun_prop) hclamp
  have heq : exteriorDomain ui a b vb =
      (Icc a b ×ˢ Icc (vb a) 0) ∩ {p : ℝ × ℝ | Γ p.1 ≤ p.2} := by
    ext p
    constructor
    · intro hp
      have hu : p.1 ∈ Icc a b := ⟨hp.2.1, hp.2.2.1⟩
      refine ⟨⟨hu, (hm ⟨le_rfl, hab⟩ hu hu.1).trans hp.2.2.2,
        hp.1.2.2.2⟩, ?_⟩
      change vb (max a (min b p.1)) ≤ p.2
      rw [min_eq_right hu.2, max_eq_right hu.1]
      exact hp.2.2.2
    · rintro ⟨⟨hu, hv⟩, hbound⟩
      have hbound' : vb p.1 ≤ p.2 := by
        change vb (max a (min b p.1)) ≤ p.2 at hbound
        simpa only [min_eq_right hu.2, max_eq_right hu.1] using hbound
      exact ⟨⟨hia.trans hu.1, hu.2.trans_lt hb,
        (hproper p.1 hu).1.le.trans hbound', hv.2⟩, hu.1, hu.2, hbound'⟩
  rw [heq]
  exact (isCompact_Icc.prod isCompact_Icc).inter_right
    (isClosed_le (hΓ.comp continuous_fst) continuous_snd)

/-- [internal]
Project a visited point to an earlier cutoff by keeping its incoming label.
Monotonicity of the boundary is exactly what keeps this projection exterior. -/
theorem min_time_mem_exteriorDomain {ui a b t : ℝ} {vb : ℝ → ℝ}
    (hia : ui ≤ a) (hm : MonotoneOn vb (Icc a b)) (ht : t ∈ Icc a b)
    {p : ℝ × ℝ} (hp : p ∈ exteriorDomain ui a b vb) :
    (min p.1 t, p.2) ∈ exteriorDomain ui a t vb := by
  have hu : p.1 ∈ Icc a b := ⟨hp.2.1, hp.2.2.1⟩
  have hmin : min p.1 t ∈ Icc a b :=
    ⟨le_min hu.1 ht.1, (min_le_left _ _).trans hu.2⟩
  exact ⟨⟨le_min hp.1.1 (hia.trans ht.1),
    (min_le_left _ _).trans_lt hp.1.2.1,
    (min_le_left _ _).trans hp.1.2.2.1, hp.1.2.2.2⟩,
    hmin.1, min_le_right _ _, (hm hmin hu (min_le_left _ _)).trans hp.2.2.2⟩

/-- [internal]
Suprema and infima over every previously visited exterior row depend
continuously on the proper finite cutoff. Only continuity on the fixed
finite exterior is needed; values of the field outside it are unrestricted.
This applies individually to all continuous field stops in `eq:cc-stop`.
No measurability-to-continuity inference is used. -/
theorem continuousOn_exterior_extrema {ui a b : ℝ} {vb : ℝ → ℝ}
    (hab : a ≤ b) (hia : ui ≤ a) (hb : b < 0)
    (hc : ContinuousOn vb (Icc a b)) (hm : MonotoneOn vb (Icc a b))
    (hproper : ∀ u ∈ Icc a b, u < vb u ∧ vb u ≤ 0)
    {f : ℝ × ℝ → ℝ} (hf : ContinuousOn f (exteriorDomain ui a b vb)) :
    ContinuousOn (fun t => sSup (f '' exteriorDomain ui a t vb)) (Icc a b) ∧
      ContinuousOn (fun t => sInf (f '' exteriorDomain ui a t vb)) (Icc a b) := by
  let K := exteriorDomain ui a b vb
  have hK : IsCompact K := isCompact_exteriorDomain hab hia hb hc hm hproper
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let F : Icc a b → K → ℝ := fun t p => f (min p.val.1 t.val, p.val.2)
  have hmem (t : Icc a b) (p : K) :
      (min p.val.1 t.val, p.val.2) ∈ K := by
    have hh := min_time_mem_exteriorDomain hia hm t.property p.property
    exact ⟨hh.1, hh.2.1, hh.2.2.1.trans t.property.2, hh.2.2.2⟩
  have hF : Continuous (Function.uncurry F) :=
    hf.comp_continuous (by fun_prop) (fun p => hmem p.1 p.2)
  have heq (t : Icc a b) : F t '' univ = f '' exteriorDomain ui a t.val vb := by
    ext y
    constructor
    · rintro ⟨p, _, rfl⟩
      exact ⟨(min p.val.1 t.val, p.val.2),
        min_time_mem_exteriorDomain hia hm t.property p.property, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      have hpK : p ∈ K := ⟨hp.1, hp.2.1, hp.2.2.1.trans t.property.2, hp.2.2.2⟩
      refine ⟨⟨p, hpK⟩, mem_univ _, ?_⟩
      dsimp only [F]
      rw [min_eq_left hp.2.2.1]
  constructor
  · rw [continuousOn_iff_continuous_domRestrict]
    apply (isCompact_univ.continuous_sSup (f := F) hF).congr
    intro t
    exact congrArg sSup (heq t)
  · rw [continuousOn_iff_continuous_domRestrict]
    apply (isCompact_univ.continuous_sInf (f := F) hF).congr
    intro t
    exact congrArg sInf (heq t)

/-- [internal]
The absolute continuous source accumulated over the exact stopped exterior
is continuous in the finite cutoff, before any absorption is used. Its zero
extension has an integrable time marginal by Fubini, and the cutoff integral
is the AC primitive of that marginal. In the closure application `F` is the
continuous weighted covariant source; the initial rough density is handled
separately by `continuousOn_initial_density_tail`. -/
theorem continuousOn_exterior_source_integral {ui a b : ℝ} {vb : ℝ → ℝ}
    (hab : a ≤ b) (hia : ui ≤ a) (hb : b < 0)
    (hc : ContinuousOn vb (Icc a b)) (hm : MonotoneOn vb (Icc a b))
    (hproper : ∀ u ∈ Icc a b, u < vb u ∧ vb u ≤ 0)
    {F : ℝ × ℝ → ℂ} (hF : ContinuousOn F (exteriorDomain ui a b vb)) :
    ContinuousOn (fun t => ∫ p in exteriorDomain ui a t vb, ‖F p‖) (Icc a b) := by
  classical
  let K := exteriorDomain ui a b vb
  have hK : IsCompact K := isCompact_exteriorDomain hab hia hb hc hm hproper
  let Q : ℝ × ℝ → ℝ := K.indicator (fun p => ‖F p‖)
  have hQi : Integrable Q (volume : Measure (ℝ × ℝ)) :=
    (integrable_indicator_iff hK.measurableSet).mpr (hF.norm.integrableOn_compact hK)
  have hQip : Integrable Q (volume.prod volume) := by
    rwa [← Measure.volume_eq_prod]
  have hprimitive :=
    hQip.integral_prod_left.intervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral
    (a := a) (b := b) left_mem_uIcc
  have hpc := hprimitive.continuousOn
  rw [uIcc_of_le hab] at hpc
  apply hpc.congr
  intro t ht
  have hslab : MeasurableSet (Icc a t ×ˢ (univ : Set ℝ)) :=
    measurableSet_Icc.prod MeasurableSet.univ
  have heq : (Icc a t ×ˢ (univ : Set ℝ)) ∩ K = exteriorDomain ui a t vb := by
    ext p
    constructor
    · rintro ⟨⟨hu, _⟩, hp⟩
      exact ⟨hp.1, hu.1, hu.2, hp.2.2.2⟩
    · intro hp
      exact ⟨⟨⟨hp.2.1, hp.2.2.1⟩, mem_univ _⟩,
        hp.1, hp.2.1, hp.2.2.1.trans ht.2, hp.2.2.2⟩
  calc
    _ = ∫ p in Icc a t ×ˢ (univ : Set ℝ), Q p := by
      rw [← integral_indicator hslab]
      dsimp only [Q]
      rw [Set.indicator_indicator, integral_indicator (hslab.inter hK.measurableSet), heq]
    _ = ∫ u in Icc a t, ∫ v, Q (u, v) := by
      rw [Measure.volume_eq_prod, setIntegral_prod Q hQip.integrableOn]
      simp only [setIntegral_univ]
    _ = _ := by
      rw [integral_Icc_eq_integral_Ioc]
      exact (intervalIntegral.integral_of_le ht.1).symm

/-- [internal]
The variation accumulated on one cylinder is continuous through its start
and finish when it is held constant outside that portion. Finiteness and
the real-value identity are consequences of the AC trace, before using
absorption. Clipping makes this portion contribute zero on earlier pieces
and its full variation on later connectors. -/
theorem continuous_clipped_variation {f : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hf : AbsolutelyContinuousOnInterval f a b) :
    Continuous (fun t => eVariationOn f (Icc a (max a (min b t)))) ∧
      Continuous (fun t => (eVariationOn f (Icc a (max a (min b t)))).toReal) := by
  have hclamp (t : ℝ) : max a (min b t) ∈ Icc a b :=
    ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩
  have hp :=
    hf.intervalIntegrable_deriv_complex.norm.absolutelyContinuousOnInterval_intervalIntegral
    left_mem_uIcc
  have hc : Continuous (fun t => ∫ x in a..max a (min b t), ‖deriv f x‖) := by
    apply hp.continuousOn.comp_continuous (by fun_prop)
    intro t
    simpa only [uIcc_of_le hab] using hclamp t
  have heq (t : ℝ) : eVariationOn f (Icc a (max a (min b t))) =
      ENNReal.ofReal (∫ x in a..max a (min b t), ‖deriv f x‖) := by
    have hsub : uIcc a (max a (min b t)) ⊆ uIcc a b := by
      rw [uIcc_of_le (hclamp t).1, uIcc_of_le hab]
      exact Icc_subset_Icc le_rfl (hclamp t).2
    exact (hf.mono hsub).eVariationOn_eq_integral_norm_deriv (hclamp t).1
  refine ⟨(ENNReal.continuous_ofReal.comp hc).congr (fun t => (heq t).symm), ?_⟩
  apply hc.congr
  intro t
  rw [heq, ENNReal.toReal_ofReal]
  exact intervalIntegral.integral_nonneg (hclamp t).1 (fun _ _ => norm_nonneg _)

/-- [internal]
The label-first source integral is exactly the integral of the continuous
source over its compact proper domain. The fixed label interval contains
the entire domain; no moving rough derivative is substituted into a limit.
There are no constants. -/
theorem sourceInteraction_eq_integral {ui e v₀ : ℝ} {S : Fields}
    (h : OriginalData ui e S) {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hproper : K ⊆ origDomain ui ∩ {p | p.1 < p.2})
    (hlabels : ∀ p ∈ K, p.2 ∈ Icc v₀ 0) :
    sourceInteraction e S K v₀ =
      ENNReal.ofReal (∫ p in K, ‖weightedJSource e S p.1 p.2‖) := by
  let f : ℝ × ℝ → ℂ := K.indicator (Function.uncurry (weightedJSource e S))
  have hi : Integrable f (volume.prod volume) :=
    (integrable_indicator_iff hK.measurableSet).mpr
      ((Renormalized.continuousOn_weightedJSource h.solution hproper).integrableOn_compact hK)
  have hsection (v : ℝ) :
      (∫⁻ u in {u | (u, v) ∈ K}, ‖weightedJSource e S u v‖ₑ) =
        ∫⁻ u, ‖f (u, v)‖ₑ := by
    have hm : MeasurableSet {u | (u, v) ∈ K} :=
      hK.measurableSet.preimage (measurable_id.prodMk measurable_const)
    rw [← lintegral_indicator hm]
    apply lintegral_congr
    intro u
    simp only [f, enorm_indicator_eq_indicator_enorm]
    rfl
  have hsupport : Function.support (fun v => ∫⁻ u, ‖f (u, v)‖ₑ) ⊆ Icc v₀ 0 := by
    intro v hv
    by_contra hn
    have hz (u : ℝ) : f (u, v) = 0 := by
      apply indicator_of_notMem
      exact fun hp => hn (hlabels (u, v) hp)
    simp only [hz, enorm_zero, lintegral_zero, Function.mem_support, ne_eq, not_true_eq_false] at hv
  unfold sourceInteraction
  simp_rw [hsection]
  rw [setLIntegral_eq_of_support_subset hsupport, ← lintegral_prod_symm _ hi.enorm.aemeasurable,
    ← ofReal_integral_norm_eq_lintegral_enorm hi]
  congr 1
  rw [← Measure.volume_eq_prod]
  simp only [f, norm_indicator_eq_indicator_norm]
  exact integral_indicator hK.measurableSet

/-- [internal]
The actual accumulated incoming interaction is continuous along any proper
finite boundary. Initial AC density supplies its fixed finite integral;
source continuity, Fubini and an AC primitive supply cutoff continuity.
This proves the accumulated-interaction component of the full stop
continuity node; the scalar extrema and finite cylinder variations are
handled by the companion theorems in this module. Constants: none. -/
theorem continuousOn_interactionNorm {ui e a b v₀ ρ : ℝ} {S : Fields}
    (h : OriginalData ui e S) {vb : ℝ → ℝ} {N : ℕ}
    (B : FiniteBoundary S ui a b v₀ ρ vb N) :
    ContinuousOn (fun t => (interactionNorm e S (exteriorDomain ui a t vb) a v₀).toReal)
      (Icc a b) := by
  have hab : a ≤ b := by
    simpa only [B.first, B.last] using B.ordered (Fin.zero_le (Fin.last N))
  have hia := (B.mem a ⟨le_rfl, hab⟩).1
  have hb := (B.mem b ⟨hab, le_rfl⟩).2.1
  have hproper (u : ℝ) (hu : u ∈ Icc a b) : u < vb u ∧ vb u ≤ 0 :=
    ⟨B.off_axis u hu, (B.mem u hu).2.2.2⟩
  have hv₀ : v₀ ≤ 0 := by simpa only [B.entry_label] using (hproper a ⟨le_rfl, hab⟩).2
  have hav₀ : a < v₀ := by simpa only [B.entry_label] using B.off_axis a ⟨le_rfl, hab⟩
  have hentry : outSeg a v₀ 0 ⊆ origDomain ui := by
    rintro ⟨u, v⟩ ⟨rfl, hv⟩
    exact ⟨hia, hav₀.trans_le hv₀, hav₀.le.trans hv.1, hv.2⟩
  have hi := Interaction.weightedJ_intervalIntegrable h.solution hav₀ hv₀ hentry
  have hini := (intervalIntegrable_iff_integrableOn_Icc_of_le hv₀).mp hi
  have hinit : initialInteraction S a v₀ ≠ ⊤ :=
    (hasFiniteIntegral_iff_enorm.mp hini.hasFiniteIntegral).ne
  have hKproper : exteriorDomain ui a b vb ⊆ origDomain ui ∩ {p | p.1 < p.2} := by
    intro p hp
    exact ⟨hp.1, (B.off_axis p.1 ⟨hp.2.1, hp.2.2.1⟩).trans_le hp.2.2.2⟩
  have hsource := continuousOn_exterior_source_integral hab hia hb B.cont B.mono hproper
    (Renormalized.continuousOn_weightedJSource h.solution hKproper)
  apply ((continuousOn_const (c := (initialInteraction S a v₀).toReal)).add hsource).congr
  intro t ht
  have hKt := isCompact_exteriorDomain ht.1 hia (ht.2.trans_lt hb)
    (B.cont.mono (Icc_subset_Icc le_rfl ht.2))
    (B.mono.mono (Icc_subset_Icc le_rfl ht.2))
    (fun u hu => hproper u ⟨hu.1, hu.2.trans ht.2⟩)
  have hsub : exteriorDomain ui a t vb ⊆ exteriorDomain ui a b vb := by
    intro p hp
    exact ⟨hp.1, hp.2.1, hp.2.2.1.trans ht.2, hp.2.2.2⟩
  have heq := sourceInteraction_eq_integral (v₀ := v₀) h hKt
    (fun p hp => hKproper (hsub hp)) (by
    intro p hp
    refine ⟨?_, hp.1.2.2.2⟩
    rw [← B.entry_label]
    exact (B.mono ⟨le_rfl, hab⟩ ⟨hp.2.1, hp.2.2.1.trans ht.2⟩ hp.2.1).trans hp.2.2.2)
  have hsum : interactionNorm e S (exteriorDomain ui a t vb) a v₀ =
      initialInteraction S a v₀ + sourceInteraction e S (exteriorDomain ui a t vb) v₀ :=
    lintegral_add_left' hini.enorm.aemeasurable _
  dsimp only [Pi.add_apply]
  rw [hsum, heq, ENNReal.toReal_add hinit ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal
    (integral_nonneg (fun p => norm_nonneg _))]; rfl

/-- [node sec:charged-closure#finite-cutoff-continuity]
All five finite-cutoff stops are continuous on a proper available finite
path. The cylinder accumulation uses each cylinder's own boundary clock,
clipped at its endpoints, and is constant on connectors. The initial L¹
density and continuous source give the actual incoming norm; the parallel
AC traces give the actual finite cylinder variations. Suprema and infima
are over the exact previously visited exterior. No estimate constants,
absorption, stage-existence or measurable-continuity premise occurs.
Source: charged_SF_new_version.tex:L4104; approved internal project record (C1)–(C2). -/
theorem finite_cutoff_continuity {ui e a b v₀ ρ : ℝ} {S : Fields}
    (h : OriginalData ui e S) {vb : ℝ → ℝ} {N : ℕ}
    (B : FiniteBoundary S ui a b v₀ ρ vb N) (T : Fin N → ℝ)
    (hT : ∀ n, 0 ≤ T n)
    (γ : ∀ n, ClockCylinder S (origDomain ui) (B.radii n) 0 (T n))
    (_hends : ∀ n, (γ n).U 0 = B.cuts n.castSucc ∧ (γ n).U (T n) = B.cool n)
    (_hgraph : ∀ n, ∀ τ ∈ Icc 0 (T n), vb ((γ n).U τ) = (γ n).V τ) :
    ContinuousOn (fun t => (interactionNorm e S (exteriorDomain ui a t vb) a v₀).toReal)
      (Icc a b) ∧
    ContinuousOn (fun t => ∑ n, (curveCovVar e S S.a (γ n).U (γ n).V 0
      (max 0 (min (T n) (cylinderClock S vb (B.cuts n.castSucc) t)))).toReal) (Icc a b) ∧
    ContinuousOn (fun t => S.r t 0) (Icc a b) ∧
    ContinuousOn (fun t => sInf ((Function.uncurry S.lam) '' exteriorDomain ui a t vb)) (Icc a b) ∧
    ContinuousOn (fun t => sSup ((fun p : ℝ × ℝ =>
      ‖S.theta p.1 p.2 / (S.lam p.1 p.2 : ℂ)‖) '' exteriorDomain ui a t vb)) (Icc a b) ∧
    ContinuousOn (fun t => sSup ((fun p : ℝ × ℝ =>
      S.mu p.1 p.2 / (1 - S.mu p.1 p.2)) '' exteriorDomain ui a t vb)) (Icc a b) := by
  have hab : a ≤ b := by
    simpa only [B.first, B.last] using B.ordered (Fin.zero_le (Fin.last N))
  have hia := (B.mem a ⟨le_rfl, hab⟩).1
  have hb := (B.mem b ⟨hab, le_rfl⟩).2.1
  let K := exteriorDomain ui a b vb
  have hproper (u : ℝ) (hu : u ∈ Icc a b) : u < vb u ∧ vb u ≤ 0 :=
    ⟨B.off_axis u hu, (B.mem u hu).2.2.2⟩
  have hsub : K ⊆ origDomain ui := fun _ hp => hp.1
  have hr (p : ℝ × ℝ) (hp : p ∈ K) : 0 < S.r p.1 p.2 :=
    h.solution.r_pos _ hp.1 ((B.off_axis p.1 ⟨hp.2.1, hp.2.2.1⟩).trans_le hp.2.2.2)
  have cr := h.solution.cont_r.mono hsub
  have cm := h.solution.cont_m.mono hsub
  have cl := h.solution.cont_lam.mono hsub
  have ct := h.solution.cont_theta.mono hsub
  have cμ : ContinuousOn (fun p : ℝ × ℝ => S.mu p.1 p.2) K :=
    (continuousOn_const.mul cm).div cr (fun p hp => (hr p hp).ne')
  have cy := (ct.div (Complex.continuous_ofReal.comp_continuousOn cl)
    (fun p hp => Complex.ofReal_ne_zero.mpr (h.solution.lam_pos _ hp.1).ne')).norm
  have cq := cμ.div (continuousOn_const.sub cμ)
    (fun p hp => (h.solution.one_sub_mu_pos _ hp.1).ne')
  have cclock (n : Fin N) : ContinuousOn (cylinderClock S vb (B.cuts n.castSucc)) (Icc a b) := by
    have cn := (h.solution.cont_nu.comp (continuousOn_id.prodMk B.cont) B.mem).neg
    have hi := cn.intervalIntegrable_of_Icc (μ := volume) hab
    have hbase : B.cuts n.castSucc ∈ uIcc a b := by
      rw [uIcc_of_le hab]
      exact ⟨B.first.ge.trans (B.ordered (Fin.zero_le _)),
        (B.ordered (Fin.le_last _)).trans B.last.le⟩
    have hc := (hi.absolutelyContinuousOnInterval_intervalIntegral hbase).continuousOn
    change ContinuousOn (fun t => ∫ x in B.cuts n.castSucc..t, -S.nu x (vb x)) (Icc a b)
    simpa only [uIcc_of_le hab, Function.comp_def,
      Function.uncurry_apply_pair, Pi.neg_apply, id_eq] using hc
  have cvar : ContinuousOn (fun t => ∑ n, (curveCovVar e S S.a (γ n).U (γ n).V 0
      (max 0 (min (T n) (cylinderClock S vb (B.cuts n.castSucc) t)))).toReal) (Icc a b) := by
    apply continuousOn_finsetSum
    intro n _
    have hac := Cylinder.ac_curveParallel_a h.solution (γ n) (B.radius_pos n) (hT n)
    have hc := (continuous_clipped_variation (hT n) hac).2
    simpa only [curveCovVar, Function.comp_def] using hc.comp_continuousOn (cclock n)
  have cR : ContinuousOn (fun t => S.r t 0) (Icc a b) :=
    h.solution.cont_r.comp (continuousOn_id.prodMk continuousOn_const)
      (fun u hu => ⟨(B.mem u hu).1, (B.mem u hu).2.1, (B.mem u hu).2.1.le, le_rfl⟩)
  exact ⟨continuousOn_interactionNorm h B, cvar, cR,
    (continuousOn_exterior_extrema hab hia hb B.cont B.mono hproper cl).2,
    (continuousOn_exterior_extrema hab hia hb B.cont B.mono hproper cy).1,
    (continuousOn_exterior_extrema hab hia hb B.cont B.mono hproper cq).1⟩

/-- [internal]
Every inward comparison point is in the triangle determined by the earliest
outgoing and latest incoming boundary labels. No expansion bound in the
interior is required for this containment. -/
theorem comparisonDomain_subset_triangle {S : Fields} {ui : ℝ} {U V : ℝ → ℝ}
    {s t b : ℝ} :
    comparisonDomain S (origDomain ui) U V s t b ⊆ triangle (U s) (V t) := by
  intro p hp
  exact ⟨hp.1.2.1.1, hp.1.1.2.2.1, hp.1.2.2.2⟩

/-- [internal]
The full row from an inward point to the existing axis stays in the same
enclosing triangle, including the axis endpoint. -/
theorem outgoing_axis_segment_subset_window {a b : ℝ} {p : ℝ × ℝ}
    (hp : p ∈ triangle a b) : outSeg p.1 p.1 p.2 ⊆ triangle a b := by
  rintro ⟨u, v⟩ ⟨hu, hv⟩
  dsimp only at hu
  subst u
  exact ⟨hp.1, hv.1, hv.2.trans hp.2.2⟩

/-- [internal]
The gap on a full window triangle is the independent late gap. This lemma
uses no exterior scalar or optical stop inside the boundary sphere. -/
theorem window_gap_of_late_geometry {S : Fields} {ui u₀ δ a b : ℝ}
    (hia : ui ≤ a) (hproper : b < 0) (hentry : u₀ ≤ a)
    (hgap : ∀ p ∈ origDomain ui, u₀ ≤ p.1 →
      0 ≤ S.mu p.1 p.2 ∧ δ ≤ 1 - S.mu p.1 p.2) :
    ∀ p ∈ triangle a b, 0 ≤ S.mu p.1 p.2 ∧ δ ≤ 1 - S.mu p.1 p.2 := by
  intro p hp
  exact hgap p (triangle_subset_origDomain hia hproper hp) (hentry.trans hp.1)

/-- [internal]
The physical charged observation scale from the produced exterior amplitude
profile. The coefficient `3` is universal and precedes every physical scale.
The profile consumer must supply `‖φ‖ ≤ M` and the scalar stop. No scalar
translation enters the estimate; the background is the actual `Fields.a`.
Source: `charged_SF_new_version.tex:L4086–L4091`. -/
theorem observation_physical_scale_of_profile {S : Fields} {u v e b R M F : ℝ}
    (hb : 0 ≤ b) (hbR : b ≤ R) (hM : 1 ≤ M) (hF : F ≤ 1)
    (hphi : ‖S.phi u v‖ ≤ M)
    (hy : ‖S.theta u v / (S.lam u v : ℂ)‖ ≤ F) :
    ‖S.a u v‖ ≤ M + F ∧
      |e| * b * (1 + ‖S.a u v‖) ≤ 3 * (|e| * M * R) := by
  have ha : ‖S.a u v‖ ≤ M + F :=
    (norm_add_le _ _).trans (add_le_add hphi hy)
  refine ⟨ha, ?_⟩
  have hsum : 1 + ‖S.a u v‖ ≤ 3 * M := by linarith
  have hM0 : 0 ≤ M := by linarith
  have hR0 : 0 ≤ R := hb.trans hbR
  calc
    _ ≤ |e| * R * (3 * M) := by gcongr
    _ = _ := by ring

/-- [internal]
A positive-radius cylinder stays strictly below the terminal boundary when
the terminal radius is larger than its cylinder radius. This derives the
proper-window endpoint condition used by cooling; it is not an additional
availability assumption. There are no estimate constants. -/
theorem cylinder_label_neg_of_radius {ui e b s t : ℝ} {S : Fields}
    (_h : OriginalData ui e S) (γ : ClockCylinder S (origDomain ui) b s t)
    (hterminal : ∀ τ ∈ Icc s t, b < S.r (γ.U τ) 0) :
    ∀ τ ∈ Icc s t, γ.V τ < 0 := by
  intro τ hτ
  have hv := (γ.mem τ hτ).2.2.2
  apply lt_of_le_of_ne hv
  intro heq
  change γ.V τ = 0 at heq
  have hr := γ.radius τ hτ
  rw [heq] at hr
  exact (hterminal τ hτ).ne' hr

/-- [internal]
Every full window inside an available cylinder has the exact enclosing
triangle and independent core gap required by `Cooling.observationInput`.
The terminal-radius separation supplies the proper last label. No optical
or scalar bound inside the sphere is used. All constants are explicit. -/
theorem observation_window_regions {ui e b T Ts u₀ δ : ℝ} {S : Fields}
    (h : OriginalData ui e S) (γ : ClockCylinder S (origDomain ui) b 0 T)
    (hb : 0 < b) (hTs : 0 ≤ Ts)
    (hentry : u₀ ≤ γ.U 0)
    (hterminal : ∀ τ ∈ Icc 0 T, b < S.r (γ.U τ) 0)
    (hgap : ∀ p ∈ origDomain ui, u₀ ≤ p.1 →
      0 ≤ S.mu p.1 p.2 ∧ δ ≤ 1 - S.mu p.1 p.2) :
    ∀ τ ∈ Icc (Ts * b) (T - Ts * b),
      triangle (γ.U (τ - Ts * b)) (γ.V (τ + Ts * b)) ⊆ origDomain ui ∧
      (∀ p ∈ triangle (γ.U (τ - Ts * b)) (γ.V (τ + Ts * b)),
        0 ≤ S.mu p.1 p.2 ∧ δ ≤ 1 - S.mu p.1 p.2) := by
  intro τ hτ
  have hwidth : 0 ≤ Ts * b := mul_nonneg hTs hb.le
  have hm : τ - Ts * b ∈ Icc 0 T := ⟨by linarith only [hτ.1], by linarith only [hτ.2, hwidth]⟩
  have hp : τ + Ts * b ∈ Icc 0 T := ⟨by linarith only [hτ.1, hwidth], by linarith only [hτ.2]⟩
  have hmp : τ - Ts * b ≤ τ + Ts * b := by linarith only [hwidth]
  have hproper := cylinder_label_neg_of_radius h γ hterminal _ hp
  have hia := (γ.mem _ hm).1
  have hzero : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hm.1.trans hm.2⟩
  refine ⟨triangle_subset_origDomain hia hproper,
    window_gap_of_late_geometry hia hproper ?_ hgap⟩
  exact hentry.trans ((γ.strictMonoOn_U h.solution).monotoneOn hzero hm hm.1)

end EmcsfAcExtension.Global.Closure
