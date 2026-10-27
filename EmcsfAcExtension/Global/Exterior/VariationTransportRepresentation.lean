module

public import EmcsfAcExtension.Global.Exterior.VariationTransport
public import EmcsfAcExtension.Global.Exterior.VariationTailsRepresentation

/-! # The literal density representation on incoming-visible hulls

Every proper incoming history has a slightly larger proper rectangular
neighborhood. The exact rectangle representation therefore gives continuity
of the literal expansion-ratio multiplier and source remainder on the whole
visible hull, including swept domains whose bounding rectangle crosses the
axis. Countably many rational rectangles give one exceptional label set
before all incoming rows. Source: `charged_SF_new_version.tex:L1410–L1416`, approved
internal project record, derivative-ac-representation (R1)–(R3).
-/

public section

open Set MeasureTheory Filter Topology Complex

namespace EmcsfAcExtension.Global.Exterior

/-- [internal] The entire proper incoming-visible region based at `a`.
Its upper label boundary is the existing last incoming cone. -/
@[expose] def densityVisibleDomain (a : ℝ) : Set (ℝ × ℝ) :=
  {p | a ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ 0}

/-- [internal] The prescribed multiplier, with the literal expansion ratio
and electromagnetic phase. No coefficient extension enters this definition. -/
@[expose] noncomputable def densityPhaseMultiplier
    (e : ℝ) (S : Fields) (a u v : ℝ) : ℂ :=
  (S.lam a v / S.lam u v : ℝ) * Complex.exp (-I * e * ∫ s in a..u, S.A s v)

/-- [internal] The literal continuous source remainder in variation of
constants, defined independently of the rough initial derivative. -/
@[expose] noncomputable def densitySourceRemainder
    (e : ℝ) (S : Fields) (a u v : ℝ) : ℂ :=
  ∫ s in a..u, (S.lam s v / S.lam u v : ℝ) *
    Complex.exp (-I * e * ∫ t in s..u, S.A t v) * rawDensitySource e S s v

/-- [internal] The canonical representative is precisely the literal
multiplier times the one fixed initial derivative, plus the source integral. -/
theorem densityRepresentative_eq_phase_source (e : ℝ) (S : Fields) (a u v : ℝ) :
    densityRepresentative e S a u v =
      densityPhaseMultiplier e S a u v * deriv (S.a a) v +
        densitySourceRemainder e S a u v :=
  densityRepresentative_def e S a u v

/-- [internal] The prescribed remainder vanishes on its anchoring row. -/
theorem densitySourceRemainder_initial (e : ℝ) (S : Fields) (a v : ℝ) :
    densitySourceRemainder e S a a v = 0 := by
  simp only [densitySourceRemainder, intervalIntegral.integral_same]

/-- [internal] Every visible incoming path lies in a proper rectangle
which is a relative neighborhood of its endpoint. The rectangle is anchored
at the original row; no bounding rectangle of a swept domain is used. -/
theorem exists_proper_density_chart {ui a : ℝ} (hua : ui ≤ a)
    {p : ℝ × ℝ} (hp : p ∈ densityVisibleDomain a) :
    ∃ x y : ℝ, a < x ∧ y < 0 ∧
      Icc a x ×ˢ Icc y 0 ⊆ origDomain ui ∩ {q | q.1 < q.2} ∧
      p ∈ Icc a x ×ˢ Icc y 0 ∧
      Icc a x ×ˢ Icc y 0 ∈ 𝓝[densityVisibleDomain a] p := by
  let x : ℝ := (2 * p.1 + p.2) / 3
  let y : ℝ := (p.1 + 2 * p.2) / 3
  have hpx : p.1 < x := by dsimp [x]; linarith [hp.2.1]
  have hxy : x < y := by dsimp [x, y]; linarith [hp.2.1]
  have hyp : y < p.2 := by dsimp [y]; linarith [hp.2.1]
  refine ⟨x, y, hp.1.trans_lt hpx, hyp.trans_le hp.2.2, ?_,
    ⟨⟨hp.1, hpx.le⟩, ⟨hyp.le, hp.2.2⟩⟩, ?_⟩
  · rintro ⟨u, v⟩ ⟨hu, hv⟩
    have huv : u < v := hu.2.trans_lt (hxy.trans_le hv.1)
    exact ⟨⟨hua.trans hu.1, huv.trans_le hv.2, huv.le, hv.2⟩, huv⟩
  · have hnx : ∀ᶠ q : ℝ × ℝ in 𝓝 p, q.1 < x :=
      continuous_fst.continuousAt.eventually (Iio_mem_nhds hpx)
    have hny : ∀ᶠ q : ℝ × ℝ in 𝓝 p, y < q.2 :=
      continuous_snd.continuousAt.eventually (Ioi_mem_nhds hyp)
    filter_upwards [self_mem_nhdsWithin,
      hnx.filter_mono nhdsWithin_le_nhds, hny.filter_mono nhdsWithin_le_nhds]
      with q hq hqx hqy
    exact ⟨⟨hq.1, hqx.le⟩, ⟨hqy.le, hq.2.2⟩⟩

/-- [node c:exterior#derivative-ac-representation]
The literal expansion-ratio phase multiplier is jointly continuous on the
entire proper visible hull. No regularity of the initial density is assumed. -/
theorem continuousOn_densityPhaseMultiplier
    {ui e a : ℝ} {S : Fields} (hS : IsSolution e S (origDomain ui)) (hua : ui ≤ a) :
    ContinuousOn (densityPhaseMultiplier e S a).uncurry (densityVisibleDomain a) := by
  intro p hp
  obtain ⟨x, y, hax, hy0, hrect, hpm, hn⟩ := exists_proper_density_chart hua hp
  have hP := (derivative_ac_representation_exact_multiplier hS hax hy0 hrect).2.1
  exact (hP p hpm).mono_of_mem_nhdsWithin hn

/-- [node c:exterior#derivative-ac-representation]
The literal source integral is jointly continuous on the visible hull,
with its zero initial remainder. Its definition uses no initial derivative. -/
theorem continuousOn_densitySourceRemainder
    {ui e a : ℝ} {S : Fields} (hS : IsSolution e S (origDomain ui)) (hua : ui ≤ a) :
    ContinuousOn (densitySourceRemainder e S a).uncurry (densityVisibleDomain a) := by
  intro p hp
  obtain ⟨x, y, hax, hy0, hrect, hpm, hn⟩ := exists_proper_density_chart hua hp
  have hR := density_source_remainder_continuousOn hS hax hy0 hrect
  exact (hR p hpm).mono_of_mem_nhdsWithin hn

/-- [node c:exterior#derivative-ac-representation]
One global null set of labels works for every visible incoming row.
Countably many rational proper rectangles are chosen before the incoming
coordinate, so the exceptional set is independent of that coordinate. -/
theorem ae_forall_densityRepresentative_hasDerivAt_visible
    {ui e a : ℝ} {S : Fields} (hS : IsSolution e S (origDomain ui)) (hua : ui ≤ a) :
    ∀ᵐ v, ∀ u : ℝ, a ≤ u → u < v → v ≤ 0 →
      HasDerivAt (S.a u) (densityRepresentative e S a u v) v := by
  have hq : ∀ᵐ v, ∀ q : ℚ × ℚ,
      (a < (q.1 : ℝ) ∧ (q.1 : ℝ) < (q.2 : ℝ) ∧ (q.2 : ℝ) < 0) →
      v ∈ Icc (q.2 : ℝ) 0 → ∀ u ∈ Icc a (q.1 : ℝ),
        HasDerivAt (S.a u) (densityRepresentative e S a u v) v := by
    apply ae_all_iff.2
    intro q
    by_cases hqm : a < (q.1 : ℝ) ∧ (q.1 : ℝ) < (q.2 : ℝ) ∧ (q.2 : ℝ) < 0
    · have hrect : Icc a (q.1 : ℝ) ×ˢ Icc (q.2 : ℝ) 0 ⊆
          origDomain ui ∩ {p | p.1 < p.2} := by
        rintro ⟨u, v⟩ ⟨hu, hv⟩
        have huv : u < v := hu.2.trans_lt (hqm.2.1.trans_le hv.1)
        exact ⟨⟨hua.trans hu.1, huv.trans_le hv.2, huv.le, hv.2⟩, huv⟩
      exact ((ae_restrict_iff' measurableSet_Icc).1
        (derivative_ac_representation_exact_multiplier hS hqm.1 hqm.2.2 hrect).1).mono
        fun v hv _ => hv
    · exact ae_of_all _ fun v hqu => (hqm hqu).elim
  filter_upwards [hq] with v hv u hau huv hv0
  obtain ⟨q, huq, hqv⟩ := exists_rat_btwn huv
  obtain ⟨r, hqr, hrv⟩ := exists_rat_btwn hqv
  exact hv (q, r) ⟨hau.trans_lt huq, hqr, hrv.trans_le hv0⟩
    ⟨hrv.le, hv0⟩ u ⟨hau, huq.le⟩

/-- [internal] A proper swept domain is contained in the incoming-visible
hull, without requiring its bounding rectangle to stay off the axis. -/
theorem variationSweptDomain_subset_visible {a b : ℝ} {V : ℝ → ℝ}
    (hproper : ∀ u ∈ Icc a b, u < V u) :
    variationSweptDomain a b V ⊆ densityVisibleDomain a := by
  intro p hp
  exact ⟨hp.1.1, (hproper p.1 hp.1).trans_le hp.2.1, hp.2.2⟩

/-- [node c:exterior#derivative-ac-representation]
The prescribed swept-domain representative has the literal continuous
multiplier and continuous zero-initial source remainder, with one fixed L¹
seed. Its outgoing derivative identity uses one exceptional label set before
all rows, even when the bounding rectangle crosses the axis. -/
theorem swept_density_representation_exact_multiplier
    {ui e a b : ℝ} {S : Fields} {V : ℝ → ℝ}
    (hS : IsSolution e S (origDomain ui)) (hab : a ≤ b)
    (hmem : ∀ u ∈ Icc a b, (u, V u) ∈ origDomain ui)
    (hproper : ∀ u ∈ Icc a b, u < V u) :
    ContinuousOn (densityPhaseMultiplier e S a).uncurry (variationSweptDomain a b V) ∧
    ContinuousOn (densitySourceRemainder e S a).uncurry (variationSweptDomain a b V) ∧
    (∀ v, densitySourceRemainder e S a a v = 0) ∧
    IntervalIntegrable (deriv (S.a a)) volume (V a) 0 ∧
    (∀ p ∈ variationSweptDomain a b V,
      densityRepresentative e S a p.1 p.2 =
        densityPhaseMultiplier e S a p.1 p.2 * deriv (S.a a) p.2 +
          densitySourceRemainder e S a p.1 p.2) ∧
    ∀ᵐ v ∂volume.restrict (Icc (V a) 0), ∀ u ∈ Icc a b, V u ≤ v →
      HasDerivAt (S.a u) (densityRepresentative e S a u v) v := by
  have hua : ui ≤ a := (hmem a ⟨le_rfl, hab⟩).1
  have hsub := variationSweptDomain_subset_visible hproper
  refine ⟨(continuousOn_densityPhaseMultiplier hS hua).mono hsub,
    (continuousOn_densitySourceRemainder hS hua).mono hsub,
    densitySourceRemainder_initial e S a,
    swept_initial_density_intervalIntegrable hS hab hmem,
    fun p _ => densityRepresentative_eq_phase_source e S a p.1 p.2, ?_⟩
  have hae : ∀ᵐ v ∂volume.restrict (Icc (V a) 0), ∀ u : ℝ,
      a ≤ u → u < v → v ≤ 0 →
        HasDerivAt (S.a u) (densityRepresentative e S a u v) v :=
    (ae_forall_densityRepresentative_hasDerivAt_visible hS hua).filter_mono
      (ae_mono Measure.restrict_le_self)
  filter_upwards [hae, ae_restrict_mem measurableSet_Icc] with v hv hvm u hu huv
  exact hv u hu.1 ((hproper u hu).trans_le huv) hvm.2

/-- [node c:exterior#derivative-ac-representation]
Every label of the exact swept representative has incoming AC transport
on its entire history from the fixed initial row. This includes exceptional
outgoing labels and the endpoints of a stopped history. Incoming derivatives
are asserted a.e. on the closed history, as in the original AC solution class. -/
theorem swept_density_representation_incoming_transport
    {ui e a b : ℝ} {S : Fields} {V : ℝ → ℝ}
    (hS : IsSolution e S (origDomain ui)) (hab : a ≤ b)
    (hmem : ∀ u ∈ Icc a b, (u, V u) ∈ origDomain ui)
    (hproper : ∀ u ∈ Icc a b, u < V u) :
    ∀ p ∈ variationSweptDomain a b V,
      AbsolutelyContinuousOnInterval (fun u => densityRepresentative e S a u p.2) a p.1 ∧
      ∀ᵐ u ∂volume.restrict (Icc a p.1),
        HasDerivAt (fun x => densityRepresentative e S a x p.2)
          (densityTransportCoefficient e S u p.2 * densityRepresentative e S a u p.2 +
            rawDensitySource e S u p.2) u := by
  intro p hp
  exact density_transport_on_incoming_history hS (hmem a ⟨le_rfl, hab⟩).1
    hp.1.1 ((hproper p.1 hp.1).trans_le hp.2.1) hp.2.2

end EmcsfAcExtension.Global.Exterior
