module

public import EmcsfAcExtension.Global.Calculus.DensityRepresentative
import EmcsfAcExtension.Infra.AC.Variation
import EmcsfAcExtension.Infra.Density.Exit

/-! # Fixed density on a swept exterior

The moving-interval argument of approved internal project record, support-moving-interval,
uses the swept set, rather than its bounding rectangle: the latter can cross
the axis. Each incoming history fits in its own proper rectangle. Continuous
extensions of the coefficient and source then give a single fixed-density
formula on the swept set. Source: `charged_SF_new_version.tex:L1337–L1340`, L1413–L1416.
-/

public section

open Set MeasureTheory Filter Topology Complex
open scoped NNReal

namespace EmcsfAcExtension.Global.Exterior

/-- [internal] The exact closed swept label domain for a proper boundary. -/
@[expose] def variationSweptDomain (a b : ℝ) (V : ℝ → ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Icc a b ∧ p.2 ∈ Icc (V p.1) 0}

/-- [internal] The ordinary incoming coefficient of the prescribed density;
its imaginary part is the connection term. -/
@[expose] noncomputable def densityTransportCoefficient
    (e : ℝ) (S : Fields) (u v : ℝ) : ℂ :=
  ((-S.nu u v / ((1 - S.mu u v) * S.r u v) *
    (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) : ℝ) : ℂ) - I * e * S.A u v

/-- [internal] Incoming past invariance of the swept domain uses only
monotonicity of the boundary label. No rectangular properness is asserted. -/
theorem variationSweptDomain_incoming {a b u v s : ℝ} {V : ℝ → ℝ}
    (hm : MonotoneOn V (Icc a b)) (hp : (u, v) ∈ variationSweptDomain a b V)
    (hs : s ∈ Icc a u) : (s, v) ∈ variationSweptDomain a b V := by
  have hsm : s ∈ Icc a b := ⟨hs.1, hs.2.trans hp.1.2⟩
  exact ⟨hsm, (hm hsm hp.1 hs.2).trans hp.2.1, hp.2.2⟩

/-- [internal] Every swept point is proper and belongs to the original
development, directly from the boundary's geometric properties. -/
theorem variationSweptDomain_subset {ui a b : ℝ} {V : ℝ → ℝ}
    (hmem : ∀ u ∈ Icc a b, (u, V u) ∈ origDomain ui)
    (hproper : ∀ u ∈ Icc a b, u < V u) :
    variationSweptDomain a b V ⊆ origDomain ui ∩ {p | p.1 < p.2} := by
  rintro ⟨u, v⟩ ⟨hu, hv⟩
  have huv := (hproper u hu).trans_le hv.1
  exact ⟨⟨(hmem u hu).1, huv.trans_le hv.2, huv.le, hv.2⟩, huv⟩

/-- [internal] A continuous swept field extends continuously to the plane by
clamping incoming time and then clamping the label to its moving interval.
The boundary need only be continuous on this proper incoming interval. -/
theorem exists_continuous_swept_extension {f : ℝ → ℝ → ℂ}
    {a b : ℝ} {V : ℝ → ℝ} (hab : a ≤ b)
    (hV : ContinuousOn V (Icc a b)) (hV0 : ∀ u ∈ Icc a b, V u ≤ 0)
    (hf : ContinuousOn f.uncurry (variationSweptDomain a b V)) :
    ∃ F : ℝ → ℝ → ℂ, Continuous F.uncurry ∧
      EqOn F.uncurry f.uncurry (variationSweptDomain a b V) := by
  let U : ℝ → ℝ := fun u => min (max a u) b
  have hU : Continuous U := by fun_prop
  have hUm (u : ℝ) : U u ∈ Icc a b :=
    ⟨le_min (le_max_left _ _) hab, min_le_right _ _⟩
  have hVU : Continuous (V ∘ U) := hV.comp_continuous hU hUm
  let π : ℝ × ℝ → ℝ × ℝ := fun p => (U p.1, min (max (V (U p.1)) p.2) 0)
  have hπ : Continuous π :=
    (hU.comp continuous_fst).prodMk
      (((hVU.comp continuous_fst).max continuous_snd).min continuous_const)
  have hπm (p : ℝ × ℝ) : π p ∈ variationSweptDomain a b V :=
    ⟨hUm p.1, le_min (le_max_left _ _) (hV0 _ (hUm p.1)), min_le_right _ _⟩
  refine ⟨fun u v => f.uncurry (π (u, v)), hf.comp_continuous hπ hπm, ?_⟩
  rintro ⟨u, v⟩ ⟨hu, hv⟩
  simp only [Function.uncurry, π, U, max_eq_right hu.1, min_eq_left hu.2,
    max_eq_right hv.1, min_eq_left hv.2]

/-- [internal] A continuous boundary gives a closed exact swept domain,
even though its unrestricted defining function can be discontinuous away
from the proper incoming interval. -/
theorem isClosed_variationSweptDomain {a b : ℝ} {V : ℝ → ℝ} (hab : a ≤ b)
    (hV : ContinuousOn V (Icc a b)) : IsClosed (variationSweptDomain a b V) := by
  let U : ℝ → ℝ := fun u => min (max a u) b
  have hU : Continuous U := by fun_prop
  have hUm (u : ℝ) : U u ∈ Icc a b :=
    ⟨le_min (le_max_left _ _) hab, min_le_right _ _⟩
  have hVU : Continuous (V ∘ U) := hV.comp_continuous hU hUm
  have heq : variationSweptDomain a b V =
      {p : ℝ × ℝ | p.1 ∈ Icc a b} ∩
        ({p : ℝ × ℝ | V (U p.1) ≤ p.2} ∩ {p : ℝ × ℝ | p.2 ≤ 0}) := by
    ext p
    by_cases hu : p.1 ∈ Icc a b
    · have hUp : U p.1 = p.1 := by simp only [U, max_eq_right hu.1, min_eq_left hu.2]
      simp only [variationSweptDomain, mem_ofPred_eq, mem_inter_iff, mem_Icc, hUp]
    · simp only [variationSweptDomain, mem_ofPred_eq, mem_inter_iff, hu, false_and]
  rw [heq]
  exact (isClosed_Icc.preimage continuous_fst).inter
    ((isClosed_le (hVU.comp continuous_fst) continuous_snd).inter
      (isClosed_le continuous_snd continuous_const))

/-- [internal] The exact swept domain is compact. Its bounding rectangle is
used only for compactness, without asserting that rectangle is proper. -/
theorem isCompact_variationSweptDomain {a b : ℝ} {V : ℝ → ℝ} (hab : a ≤ b)
    (hV : ContinuousOn V (Icc a b)) (hm : MonotoneOn V (Icc a b)) :
    IsCompact (variationSweptDomain a b V) := by
  apply (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset
    (isClosed_variationSweptDomain hab hV)
  · intro p hp
    exact ⟨hp.1, (hm ⟨le_rfl, hab⟩ hp.1 hp.1.1).trans hp.2.1, hp.2.2⟩

/-- [node c:exterior#derivative-ac-representation]
Every proper incoming history has the canonical density's incoming AC
equation at every label. A larger proper rectangle around this single history
supplies the sectional theorem, including the case of a zero-length history.
The endpoint and initial-row conditions are purely geometric. -/
theorem density_transport_on_incoming_history
    {ui e a t v : ℝ} {S : Fields} (hS : IsSolution e S (origDomain ui))
    (hua : ui ≤ a) (hat : a ≤ t) (htv : t < v) (hv0 : v ≤ 0) :
    AbsolutelyContinuousOnInterval (fun u => densityRepresentative e S a u v) a t ∧
      ∀ᵐ u ∂volume.restrict (Icc a t),
        HasDerivAt (fun x => densityRepresentative e S a x v)
          (densityTransportCoefficient e S u v * densityRepresentative e S a u v +
            rawDensitySource e S u v) u := by
  let x : ℝ := (t + v) / 2
  let c : ℝ := (x + v) / 2
  have htx : t < x := by dsimp [x]; linarith
  have hxc : x < c := by dsimp [c, x]; linarith
  have hcv : c < v := by dsimp [c, x]; linarith
  have hax : a < x := hat.trans_lt htx
  have hc0 : c < 0 := hcv.trans_le hv0
  have hrect : Icc a x ×ˢ Icc c 0 ⊆ origDomain ui ∩ {p | p.1 < p.2} := by
    rintro ⟨u, w⟩ ⟨hu, hw⟩
    have huw := hu.2.trans_lt (hxc.trans_le hw.1)
    exact ⟨⟨hua.trans hu.1, huw.trans_le hw.2, huw.le, hw.2⟩, huw⟩
  have h := Calculus.weak_outgoing_density_transport hS hax hc0 hrect v ⟨hcv.le, hv0⟩
  have hsub : uIcc a t ⊆ uIcc a x := by
    rw [uIcc_of_le hat, uIcc_of_le hax.le]
    exact Icc_subset_Icc le_rfl htx.le
  refine ⟨h.1.mono hsub, ?_⟩
  exact h.2.filter_mono (ae_mono (Measure.restrict_mono
    (Icc_subset_Icc le_rfl htx.le) le_rfl))

/-- [internal] At a proper initial point the prescribed representative is
exactly the fixed initial derivative, including at exceptional labels. -/
theorem densityRepresentative_initial_of_mem
    {ui e a v : ℝ} {S : Fields} (hS : IsSolution e S (origDomain ui))
    (hp : (a, v) ∈ origDomain ui) :
    densityRepresentative e S a a v = deriv (S.a a) v := by
  simp [densityRepresentative, (hS.lam_pos (a, v) hp).ne']

/-- [internal] Continuous coefficient and source extensions identify one
transport formula everywhere on the swept set. The extension values away
from that set play no role in any incoming history. -/
theorem densityRepresentative_eq_transportDensity_on_swept
    {ui e a b : ℝ} {S : Fields} {V : ℝ → ℝ}
    (hS : IsSolution e S (origDomain ui)) (hab : a ≤ b)
    (hm : MonotoneOn V (Icc a b))
    (hmem : ∀ u ∈ Icc a b, (u, V u) ∈ origDomain ui)
    (hproper : ∀ u ∈ Icc a b, u < V u)
    {C F : ℝ → ℝ → ℂ} (hC : Continuous C.uncurry) (hF : Continuous F.uncurry)
    (hCe : EqOn C.uncurry (densityTransportCoefficient e S).uncurry
      (variationSweptDomain a b V))
    (hFe : EqOn F.uncurry (rawDensitySource e S).uncurry (variationSweptDomain a b V)) :
    ∀ p ∈ variationSweptDomain a b V,
      densityRepresentative e S a p.1 p.2 =
        Density.transportDensity C F (deriv (S.a a)) a p.1 p.2 := by
  intro p hp
  have hK := variationSweptDomain_subset hmem hproper
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have htp := density_transport_on_incoming_history hS (hmem a ha).1 hp.1.1
    (hK hp).2 hp.2.2
  have hcv : IntervalIntegrable (fun u => C u p.2) volume a p.1 :=
    ((hC.comp (continuous_id.prodMk continuous_const))).intervalIntegrable _ _
  have hfv : IntervalIntegrable (fun u => F u p.2) volume a p.1 :=
    ((hF.comp (continuous_id.prodMk continuous_const))).intervalIntegrable _ _
  apply Density.eq_transportDensity_of_ac_deriv_eq hp.1.1 htp.1 hcv hfv ?_ ?_ p.1
    ⟨hp.1.1, le_rfl⟩
  · filter_upwards [htp.2, ae_restrict_mem measurableSet_Icc] with u hu hum
    have hsm := variationSweptDomain_incoming hm hp hum
    have hc : C u p.2 = densityTransportCoefficient e S u p.2 := hCe hsm
    have hf : F u p.2 = rawDensitySource e S u p.2 := hFe hsm
    rw [hu.deriv, hc, hf]
  · exact densityRepresentative_initial_of_mem hS
      (hK (variationSweptDomain_incoming hm hp ⟨le_rfl, hp.1.1⟩)).1

/-- [node c:exterior#derivative-ac-representation]
A single pair of continuous factors represents the prescribed density on
the entire proper swept domain, with its actual initial derivative. The
factors are globally continuous extensions; no field equation or positive
radius is required on the bounding rectangle that may cross the axis. -/
theorem exists_swept_density_factors
    {ui e a b : ℝ} {S : Fields} {V : ℝ → ℝ}
    (hS : IsSolution e S (origDomain ui)) (hab : a ≤ b)
    (hV : ContinuousOn V (Icc a b)) (hm : MonotoneOn V (Icc a b))
    (hmem : ∀ u ∈ Icc a b, (u, V u) ∈ origDomain ui)
    (hproper : ∀ u ∈ Icc a b, u < V u) :
    ∃ P R : ℝ → ℝ → ℂ, Continuous P.uncurry ∧ Continuous R.uncurry ∧
      ∀ p ∈ variationSweptDomain a b V,
        densityRepresentative e S a p.1 p.2 =
          Density.fixedDensity P R (deriv (S.a a)) p.1 p.2 := by
  have hK := variationSweptDomain_subset hmem hproper
  have hV0 (u : ℝ) (hu : u ∈ Icc a b) : V u ≤ 0 := (hmem u hu).2.2.2
  obtain ⟨C, hC, hCe⟩ := exists_continuous_swept_extension
    (f := densityTransportCoefficient e S) hab hV hV0
    (Calculus.continuousOn_density_coefficient hS hK)
  obtain ⟨F, hF, hFe⟩ := exists_continuous_swept_extension hab hV hV0
    (Calculus.continuousOn_rawDensitySource hS hK)
  obtain ⟨P, R, hP, hR, hPR⟩ := Density.exists_continuous_transport_factors hC hF a
  refine ⟨P, R, hP, hR, ?_⟩
  intro p hp
  exact (densityRepresentative_eq_transportDensity_on_swept hS hab hm hmem hproper
    hC hF hCe hFe p hp).trans (hPR _ _ _)

/-- [internal] The fixed initial density is L¹ over the complete initial
label interval of a proper swept exterior. No outgoing derivative bound is
assumed. -/
theorem swept_initial_density_intervalIntegrable
    {ui e a b : ℝ} {S : Fields} {V : ℝ → ℝ}
    (hS : IsSolution e S (origDomain ui)) (hab : a ≤ b)
    (hmem : ∀ u ∈ Icc a b, (u, V u) ∈ origDomain ui) :
    IntervalIntegrable (deriv (S.a a)) volume (V a) 0 := by
  have ha := hmem a ⟨le_rfl, hab⟩
  apply (hS.ac_out a (V a) 0 ha.2.2.2 ?_).2.2.2.2.intervalIntegrable_deriv_complex
  rintro ⟨u, v⟩ ⟨rfl, hv⟩
  exact ⟨ha.1, ha.2.1, ha.2.2.1.trans hv.1, hv.2⟩

/-- [internal] The uniform swept-domain majorant is an L¹ function of the
initial label. Its positive constant depends on this solution, coupling,
boundary and proper interval, and is fixed before both coordinates vary.
There is no asserted uniformity at the missing endpoint. -/
theorem exists_swept_density_bound
    {ui e a b : ℝ} {S : Fields} {V : ℝ → ℝ}
    (hS : IsSolution e S (origDomain ui)) (hab : a ≤ b)
    (hV : ContinuousOn V (Icc a b)) (hm : MonotoneOn V (Icc a b))
    (hmem : ∀ u ∈ Icc a b, (u, V u) ∈ origDomain ui)
    (hproper : ∀ u ∈ Icc a b, u < V u) :
    ∃ C : ℝ, 0 < C ∧
      IntervalIntegrable (fun v => C * (‖deriv (S.a a) v‖ + 1)) volume (V a) 0 ∧
      ∀ p ∈ variationSweptDomain a b V,
        ‖densityRepresentative e S a p.1 p.2‖ ≤ C * (‖deriv (S.a a) p.2‖ + 1) := by
  obtain ⟨P, R, hP, hR, heq⟩ := exists_swept_density_factors hS hab hV hm hmem hproper
  obtain ⟨C, hC, hbound⟩ := Density.exists_fixedDensity_bound
    (hP.continuousOn (s := Icc a b ×ˢ Icc (V a) 0)) hR.continuousOn
  refine ⟨C, hC, ((swept_initial_density_intervalIntegrable hS hab hmem).norm.add
    intervalIntegrable_const).const_mul C, ?_⟩
  intro p hp
  rw [heq p hp]
  exact hbound _ _ hp.1 _ ⟨(hm ⟨le_rfl, hab⟩ hp.1 hp.1.1).trans hp.2.1, hp.2.2⟩

/-- [internal] Zero extension of the canonical swept density is Borel.
This gives an actual measurable representative for stopped-history Tonelli,
rather than restricting a product-almost-everywhere derivative to exits. -/
theorem measurable_stopped_swept_density
    {ui e a b : ℝ} {S : Fields} {V : ℝ → ℝ}
    (hS : IsSolution e S (origDomain ui)) (hab : a ≤ b)
    (hV : ContinuousOn V (Icc a b)) (hm : MonotoneOn V (Icc a b))
    (hmem : ∀ u ∈ Icc a b, (u, V u) ∈ origDomain ui)
    (hproper : ∀ u ∈ Icc a b, u < V u) :
    Measurable ((variationSweptDomain a b V).indicator
      (fun p => densityRepresentative e S a p.1 p.2)) := by
  obtain ⟨P, R, hP, hR, heq⟩ := exists_swept_density_factors hS hab hV hm hmem hproper
  have hW := Density.measurable_fixedDensity hP.measurable hR.measurable
    (measurable_deriv (S.a a))
  have hid : (variationSweptDomain a b V).indicator
      (fun p => densityRepresentative e S a p.1 p.2) =
      (variationSweptDomain a b V).indicator
        (Density.fixedDensity P R (deriv (S.a a))).uncurry := by
    funext p
    by_cases hp : p ∈ variationSweptDomain a b V
    · simp only [indicator_of_mem hp, Function.uncurry, heq p hp]
    · simp only [indicator_of_notMem hp]
  rw [hid]
  exact hW.indicator (isClosed_variationSweptDomain hab hV).measurableSet

/-- [node c:exterior#boundary-derivative-integrability]
Every measurable exit whose graph lies in the swept domain has an L¹
prescribed density. Its integrability follows from the fixed initial L¹
density and the continuous factors; no boundary-density premise is added.
The label interval can include both exited and surviving labels. -/
theorem intervalIntegrable_swept_density_exit
    {ui e a b c d : ℝ} {S : Fields} {V τ : ℝ → ℝ}
    (hS : IsSolution e S (origDomain ui)) (hab : a ≤ b) (hcd : c ≤ d)
    (hV : ContinuousOn V (Icc a b)) (hm : MonotoneOn V (Icc a b))
    (hmem : ∀ u ∈ Icc a b, (u, V u) ∈ origDomain ui)
    (hproper : ∀ u ∈ Icc a b, u < V u) (hτ : Measurable τ)
    (hτmem : ∀ v ∈ Icc c d, (τ v, v) ∈ variationSweptDomain a b V) :
    IntervalIntegrable (fun v => densityRepresentative e S a (τ v) v) volume c d := by
  obtain ⟨P, R, hP, hR, heq⟩ := exists_swept_density_factors hS hab hV hm hmem hproper
  obtain ⟨C, hC, hI, hb⟩ := exists_swept_density_bound hS hab hV hm hmem hproper
  have hV0 := (hmem a ⟨le_rfl, hab⟩).2.2.2
  have hsub : uIcc c d ⊆ uIcc (V a) 0 := by
    rw [uIcc_of_le hcd, uIcc_of_le hV0]
    intro v hv
    have hp := hτmem v hv
    exact ⟨(hm ⟨le_rfl, hab⟩ hp.1 hp.1.1).trans hp.2.1, hp.2.2⟩
  have hmW : Measurable (fun v => Density.fixedDensity P R (deriv (S.a a)) (τ v) v) :=
    ((hP.measurable.comp (hτ.prodMk measurable_id)).mul (measurable_deriv (S.a a))).add
      (hR.measurable.comp (hτ.prodMk measurable_id))
  have he : (fun v => Density.fixedDensity P R (deriv (S.a a)) (τ v) v) =ᵐ[
      volume.restrict (Icc c d)] (fun v => densityRepresentative e S a (τ v) v) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    exact (heq _ (hτmem v hv)).symm
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hcd).2
  apply Integrable.mono'
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hcd).1 (hI.mono_set hsub))
    (hmW.aestronglyMeasurable.congr he)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
  exact hb _ (hτmem v hv)

/-- [node c:exterior#boundary-derivative-integrability]
The boundary integral equals its labelwise exit integral on the actual swept
domain. Boundary integrability is a conclusion. The constants `K,L` are the
local forward and inverse Lipschitz bounds of this proper segment. -/
theorem swept_density_boundary_integral_eq_exit
    {ui e a b : ℝ} {S : Fields} {V τ : ℝ → ℝ} {K L : ℝ≥0}
    (hS : IsSolution e S (origDomain ui)) (hab : a ≤ b)
    (hV : LipschitzOnWith K V (uIcc a b)) (hm : MonotoneOn V (uIcc a b))
    (ha : AntilipschitzWith L ((uIcc a b).domRestrict V))
    (hmem : ∀ u ∈ uIcc a b, (u, V u) ∈ origDomain ui)
    (hproper : ∀ u ∈ uIcc a b, u < V u) (hτ : Measurable τ)
    (hτmem : ∀ v ∈ Icc (V a) (V b), (τ v, v) ∈ variationSweptDomain a b V)
    (hexit : ∀ u ∈ uIcc a b, τ (V u) = u) :
    IntervalIntegrable (fun u => deriv V u • densityRepresentative e S a u (V u))
      volume a b ∧
      (∫ u in a..b, deriv V u • densityRepresentative e S a u (V u)) =
        ∫ v in V a..V b, densityRepresentative e S a (τ v) v := by
  apply Density.integral_boundary_eq_exit hV hm ha hexit
  apply intervalIntegrable_swept_density_exit hS hab
    (hm left_mem_uIcc right_mem_uIcc hab)
  · simpa only [uIcc_of_le hab] using hV.continuousOn
  · simpa only [uIcc_of_le hab] using hm
  · simpa only [uIcc_of_le hab] using hmem
  · simpa only [uIcc_of_le hab] using hproper
  · exact hτ
  · exact hτmem

/-- [internal] The real exit cost equals the weighted boundary norm on the
actual swept domain. This is the exit term in the moving-interval modulus
estimate; integrability of both costs is derived from the fixed density. -/
theorem swept_density_boundary_norm_eq_exit
    {ui e a b : ℝ} {S : Fields} {V τ : ℝ → ℝ} {K L : ℝ≥0}
    (hS : IsSolution e S (origDomain ui)) (hab : a ≤ b)
    (hV : LipschitzOnWith K V (uIcc a b)) (hm : MonotoneOn V (uIcc a b))
    (ha : AntilipschitzWith L ((uIcc a b).domRestrict V))
    (hmem : ∀ u ∈ uIcc a b, (u, V u) ∈ origDomain ui)
    (hproper : ∀ u ∈ uIcc a b, u < V u) (hτ : Measurable τ)
    (hτmem : ∀ v ∈ Icc (V a) (V b), (τ v, v) ∈ variationSweptDomain a b V)
    (hexit : ∀ u ∈ uIcc a b, τ (V u) = u) :
    IntervalIntegrable (fun u => deriv V u * ‖densityRepresentative e S a u (V u)‖)
      volume a b ∧
      (∫ u in a..b, deriv V u * ‖densityRepresentative e S a u (V u)‖) =
        ∫ v in V a..V b, ‖densityRepresentative e S a (τ v) v‖ := by
  have hi : IntervalIntegrable (fun v => densityRepresentative e S a (τ v) v)
      volume (V a) (V b) := by
    apply intervalIntegrable_swept_density_exit hS hab
      (hm left_mem_uIcc right_mem_uIcc hab)
    · simpa only [uIcc_of_le hab] using hV.continuousOn
    · simpa only [uIcc_of_le hab] using hm
    · simpa only [uIcc_of_le hab] using hmem
    · simpa only [uIcc_of_le hab] using hproper
    · exact hτ
    · exact hτmem
  exact Density.integral_boundary_eq_exit (W := fun u v =>
    ‖densityRepresentative e S a u v‖) hV hm ha hexit hi.norm

/-- [node c:exterior#derivative-ac-representation]
On each swept row the same selected density is L¹ and is an everywhere
outgoing primitive of the normalized scalar. The proper rectangle used for
this one row is anchored at the original row `a`; its upper incoming edge
lies strictly before this row's boundary label. -/
theorem swept_density_row_primitive
    {ui e a b u : ℝ} {S : Fields} {V : ℝ → ℝ}
    (hS : IsSolution e S (origDomain ui)) (hab : a ≤ b)
    (hmem : ∀ u ∈ Icc a b, (u, V u) ∈ origDomain ui)
    (hproper : ∀ u ∈ Icc a b, u < V u) (hu : u ∈ Icc a b) :
    IntervalIntegrable (densityRepresentative e S a u) volume (V u) 0 ∧
      ∀ v ∈ Icc (V u) 0,
        S.a u v = S.a u (V u) + ∫ w in V u..v, densityRepresentative e S a u w := by
  have hV0 : V u ≤ 0 := (hmem u hu).2.2.2
  rcases lt_or_eq_of_le hV0 with hV0 | hV0
  · let x : ℝ := (u + V u) / 2
    have hux : u < x := by dsimp [x]; linarith only [hproper u hu]
    have hxV : x < V u := by dsimp [x]; linarith only [hproper u hu]
    have hax := hu.1.trans_lt hux
    have hrect : Icc a x ×ˢ Icc (V u) 0 ⊆ origDomain ui ∩ {p | p.1 < p.2} := by
      rintro ⟨s, v⟩ ⟨hs, hv⟩
      have hsv := hs.2.trans_lt (hxV.trans_le hv.1)
      exact ⟨⟨(hmem a ⟨le_rfl, hab⟩).1.trans hs.1, hsv.trans_le hv.2,
        hsv.le, hv.2⟩, hsv⟩
    obtain ⟨P, R, hP, hR, heq, hprim⟩ := Calculus.exists_density_factors hS hax hV0 hrect
    have hinit := (hS.ac_out a (V u) 0 hV0.le (by
      rintro ⟨s, v⟩ ⟨rfl, hv⟩
      exact (hrect ⟨⟨le_rfl, hax.le⟩, hv⟩).1)).2.2.2.2
    have hum : u ∈ Icc a x := ⟨hu.1, hux.le⟩
    have hi := Density.intervalIntegrable_fixedDensity hV0.le hum hP hR
      hinit.intervalIntegrable_deriv_complex
    refine ⟨hi.congr_ae ?_, ?_⟩
    · apply (ae_restrict_iff' measurableSet_uIoc).2
      filter_upwards [] with v hv
      rw [uIoc_of_le hV0.le] at hv
      exact (heq u hum v (Ioc_subset_Icc_self hv)).symm
    · intro v hv
      rw [hprim u hum v hv]
      congr 1
      apply intervalIntegral.integral_congr
      intro w hw
      rw [uIcc_of_le hv.1] at hw
      exact (heq u hum w ⟨hw.1, hw.2.trans hv.2⟩).symm
  · rw [hV0]
    refine ⟨IntervalIntegrable.refl, ?_⟩
    intro v hv
    have hv0 : v = 0 := le_antisymm hv.2 hv.1
    simp only [hv0, intervalIntegral.integral_same, add_zero]

/-- [internal] The actual row variation is exactly the norm integral of
the canonical density anchored at the single initial row. Thus variation
estimates and moving-domain dominated convergence use the same representative.
There are no constants. -/
theorem swept_row_variation_eq_density_integral
    {ui e a b u : ℝ} {S : Fields} {V : ℝ → ℝ}
    (hS : IsSolution e S (origDomain ui)) (hab : a ≤ b)
    (hmem : ∀ u ∈ Icc a b, (u, V u) ∈ origDomain ui)
    (hproper : ∀ u ∈ Icc a b, u < V u) (hu : u ∈ Icc a b) :
    (eVariationOn (S.a u) (Icc (V u) 0)).toReal =
      ∫ v in V u..0, ‖densityRepresentative e S a u v‖ := by
  obtain ⟨hi, hprim⟩ := swept_density_row_primitive hS hab hmem hproper hu
  rw [hi.eVariationOn_eq_integral_norm_of_eq_integral (hmem u hu).2.2.2 hprim,
    ENNReal.toReal_ofReal (intervalIntegral.integral_nonneg (hmem u hu).2.2.2
      (fun _ _ => norm_nonneg _))]

end EmcsfAcExtension.Global.Exterior
