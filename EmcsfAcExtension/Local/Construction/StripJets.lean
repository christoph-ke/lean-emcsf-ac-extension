module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Differentiating the rectangle's transverse primitives

Once joint C¹ regularity has been recovered, differentiation under the
actual integrals gives internal project record (47). Uniform domination comes from
continuous first jets on the compact rectangle. No second derivative of
the state or entering traces occurs.
-/

public section

open Set Filter MeasureTheory
open scoped Topology

namespace EmcsfAcExtension.Local

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The incoming first jet of a state on a specified closed rectangle. -/
@[expose] noncomputable def rectangleJetU (a b c d : ℝ) (F : ℝ × ℝ → E)
    (p : ℝ × ℝ) : E := fderivWithin ℝ F (Icc a b ×ˢ Icc c d) p (1,0)

/-- The outgoing first jet of a state on a specified closed rectangle. -/
@[expose] noncomputable def rectangleJetV (a b c d : ℝ) (F : ℝ × ℝ → E)
    (p : ℝ × ℝ) : E := fderivWithin ℝ F (Icc a b ×ˢ Icc c d) p (0,1)

/-- The incoming jet of a C¹ rectangle state is jointly continuous. -/
theorem continuousOn_rectangleJetU {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    {F : ℝ × ℝ → E} (hF : ContDiffOn ℝ 1 F (Icc a b ×ˢ Icc c d)) :
    ContinuousOn (rectangleJetU a b c d F) (Icc a b ×ˢ Icc c d) := by
  exact (hF.continuousOn_fderivWithin ((uniqueDiffOn_Icc hab).prod (uniqueDiffOn_Icc hcd))
    (by decide)).clm_apply continuousOn_const

/-- The outgoing jet of a C¹ rectangle state is jointly continuous. -/
theorem continuousOn_rectangleJetV {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    {F : ℝ × ℝ → E} (hF : ContDiffOn ℝ 1 F (Icc a b ×ˢ Icc c d)) :
    ContinuousOn (rectangleJetV a b c d F) (Icc a b ×ˢ Icc c d) := by
  exact (hF.continuousOn_fderivWithin ((uniqueDiffOn_Icc hab).prod (uniqueDiffOn_Icc hcd))
    (by decide)).clm_apply continuousOn_const

/-- Restricting a C¹ rectangle state to an incoming section identifies
its canonical incoming jet, including the endpoints. -/
theorem hasDerivWithinAt_rectangleJetU {a b c d u v : ℝ}
    {F : ℝ × ℝ → E} (hF : ContDiffOn ℝ 1 F (Icc a b ×ˢ Icc c d))
    (hu : u ∈ Icc a b) (hv : v ∈ Icc c d) :
    HasDerivWithinAt (fun s => F (s,v)) (rectangleJetU a b c d F (u,v)) (Icc a b) u := by
  have hline : HasDerivWithinAt (fun s : ℝ => (s,v)) (1,0) (Icc a b) u :=
    (hasDerivWithinAt_id u (Icc a b)).prodMk (hasDerivWithinAt_const u (Icc a b) v)
  exact ((hF.differentiableOn (by decide) (u,v) ⟨hu,hv⟩).hasFDerivWithinAt).comp_hasDerivWithinAt u
    hline (show MapsTo (fun s : ℝ => (s,v)) (Icc a b) (Icc a b ×ˢ Icc c d) from
      fun s hs => ⟨hs,hv⟩)

/-- Restricting a C¹ rectangle state to an outgoing section identifies
its canonical outgoing jet, including the endpoints. -/
theorem hasDerivWithinAt_rectangleJetV {a b c d u v : ℝ}
    {F : ℝ × ℝ → E} (hF : ContDiffOn ℝ 1 F (Icc a b ×ˢ Icc c d))
    (hu : u ∈ Icc a b) (hv : v ∈ Icc c d) :
    HasDerivWithinAt (fun t => F (u,t)) (rectangleJetV a b c d F (u,v)) (Icc c d) v := by
  exact ((hF.differentiableOn (by decide) (u,v) ⟨hu,hv⟩).hasFDerivWithinAt).comp_hasDerivWithinAt v
    ((hasDerivWithinAt_const v (Icc c d) u).prodMk (hasDerivWithinAt_id v (Icc c d)))
    (fun t ht => ⟨hu,ht⟩)

/-- Differentiation under a fixed outgoing primitive at an interior
incoming parameter. Domination uses a finite bound on the continuous
first jet over the whole rectangle, without any second derivative. -/
theorem hasDerivAt_integral_rectangleJetU {a b c d u v : ℝ}
    (hab : a < b) (hcd : c < d) {F : ℝ × ℝ → E}
    (hF : ContDiffOn ℝ 1 F (Icc a b ×ˢ Icc c d))
    (hu : u ∈ Ioo a b) (hv : v ∈ Icc c d) :
    HasDerivAt (fun s => ∫ t in c..v, F (s,t))
      (∫ t in c..v, rectangleJetU a b c d F (u,t)) u := by
  have hJ := continuousOn_rectangleJetU hab hcd hF
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hJ
  have hsec (s : ℝ) (hs : s ∈ Icc a b) : ContinuousOn (fun t => F (s,t)) (Icc c v) :=
    hF.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => ⟨hs, ⟨ht.1,ht.2.trans hv.2⟩⟩)
  have hJsec : ContinuousOn (fun t => rectangleJetU a b c d F (u,t)) (Icc c v) :=
    hJ.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => ⟨⟨hu.1.le,hu.2.le⟩, ⟨ht.1,ht.2.trans hv.2⟩⟩)
  have hmeas : ∀ᶠ s in 𝓝 u,
      AEStronglyMeasurable (fun t => F (s,t)) (volume.restrict (Ioc c v)) := by
    filter_upwards [Ioo_mem_nhds hu.1 hu.2] with s hs
    exact ((hsec s ⟨hs.1.le,hs.2.le⟩).intervalIntegrable_of_Icc hv.1).1.aestronglyMeasurable
  have hbound : ∀ᵐ t ∂(volume.restrict (Ioc c v)), ∀ s ∈ Ioo a b,
      ‖rectangleJetU a b c d F (s,t)‖ ≤ B := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    intro s hs
    exact hB (s,t) ⟨⟨hs.1.le,hs.2.le⟩, ⟨ht.1.le,ht.2.trans hv.2⟩⟩
  have hdiff : ∀ᵐ t ∂(volume.restrict (Ioc c v)), ∀ s ∈ Ioo a b,
      HasDerivAt (fun x => F (x,t)) (rectangleJetU a b c d F (s,t)) s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    intro s hs
    exact (hasDerivWithinAt_rectangleJetU hF ⟨hs.1.le,hs.2.le⟩
      ⟨ht.1.le,ht.2.trans hv.2⟩).hasDerivAt (Icc_mem_nhds hs.1 hs.2)
  have hi := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioc c v)) (F := fun s t => F (s,t))
    (F' := fun s t => rectangleJetU a b c d F (s,t)) (bound := fun _ => B)
    (Ioo_mem_nhds hu.1 hu.2) hmeas
    ((hsec u ⟨hu.1.le,hu.2.le⟩).intervalIntegrable_of_Icc hv.1).1
    ((hJsec.intervalIntegrable_of_Icc hv.1).1.aestronglyMeasurable) hbound
    (continuous_const.intervalIntegrable c v).1 hdiff
  simpa only [intervalIntegral.integral_of_le hv.1] using hi.2

/-- A continuous rectangle density has a continuous outgoing primitive
as a function of the incoming parameter, including the parameter sides. -/
theorem continuousOn_integral_rectangle {a b c d v : ℝ} (hcd : c ≤ d)
    {F : ℝ × ℝ → E} (hF : ContinuousOn F (Icc a b ×ˢ Icc c d))
    (hv : v ∈ Icc c d) :
    ContinuousOn (fun s => ∫ t in c..v, F (s,t)) (Icc a b) := by
  let G : Icc a b → ℝ → E := fun s t => F (s, projIcc c d hcd t)
  have hG : Continuous (Function.uncurry G) :=
    hF.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp (continuous_projIcc.comp continuous_snd)))
      (fun p => ⟨p.1.2, (projIcc c d hcd p.2).2⟩)
  have hi := continuous_parametric_integral_of_continuous (μ := volume) hG
    (isCompact_Icc : IsCompact (Icc c v))
  rw [continuousOn_iff_continuous_domRestrict]
  apply hi.congr
  intro u
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hv.1]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hv.1] at ht
  have ht' : t ∈ Icc c d := ⟨ht.1,ht.2.trans hv.2⟩
  simp only [G, projIcc_of_mem hcd ht']

/-- Differentiating a genuine outgoing primitive identity gives its
incoming first-jet integral identity on the entire closed interval.
Endpoint validity follows from continuity of first jets and the density
of the interior, rather than any second derivative. -/
theorem derivWithin_eq_add_integral_rectangleJetU {a b c d v : ℝ}
    (hab : a < b) (hcd : c < d) {f xb : ℝ → E} {G : ℝ × ℝ → E}
    (hf : ContDiffOn ℝ 1 f (Icc a b)) (hxb : ContDiffOn ℝ 1 xb (Icc a b))
    (hG : ContDiffOn ℝ 1 G (Icc a b ×ˢ Icc c d)) (hv : v ∈ Icc c d)
    (heq : ∀ u ∈ Icc a b, f u = xb u + ∫ t in c..v, G (u, t)) :
    ∀ u ∈ Icc a b, derivWithin f (Icc a b) u = derivWithin xb (Icc a b) u +
      ∫ t in c..v, rectangleJetU a b c d G (u,t) := by
  have hleft := (contDiffOn_one_iff_derivWithin (uniqueDiffOn_Icc hab)).mp hf |>.2
  have hright := ((contDiffOn_one_iff_derivWithin (uniqueDiffOn_Icc hab)).mp hxb |>.2).add
    (continuousOn_integral_rectangle hcd.le (continuousOn_rectangleJetU hab hcd hG) hv)
  have hint : EqOn (derivWithin f (Icc a b))
      (fun u => derivWithin xb (Icc a b) u +
        ∫ t in c..v, rectangleJetU a b c d G (u,t)) (Ioo a b) := by
    intro u hu
    have hu' : u ∈ Icc a b := ⟨hu.1.le,hu.2.le⟩
    have hd := (hxb.differentiableOn (by decide) u hu').hasDerivWithinAt.hasDerivAt
      (Icc_mem_nhds hu.1 hu.2)
    have hi := hasDerivAt_integral_rectangleJetU hab hcd hG hu hv
    have hevent : f =ᶠ[𝓝 u] fun s => xb s + ∫ t in c..v, G (s,t) := by
      filter_upwards [Icc_mem_nhds hu.1 hu.2] with s hs
      exact heq s hs
    exact ((hf.differentiableOn (by decide) u hu').hasDerivWithinAt.hasDerivAt
      (Icc_mem_nhds hu.1 hu.2)).unique ((hd.add hi).congr_of_eventuallyEq hevent)
  exact hint.of_subset_closure hleft hright Ioo_subset_Icc_self
    (by rw [closure_Ioo hab.ne])

/-- Differentiation under an incoming primitive at an interior outgoing
parameter, using only a compact bound on continuous first jets. -/
theorem hasDerivAt_integral_rectangleJetV {a b c d u v : ℝ}
    (hab : a < b) (hcd : c < d) {F : ℝ × ℝ → E}
    (hF : ContDiffOn ℝ 1 F (Icc a b ×ˢ Icc c d))
    (hu : u ∈ Icc a b) (hv : v ∈ Ioo c d) :
    HasDerivAt (fun s => ∫ t in a..u, F (t,s))
      (∫ t in a..u, rectangleJetV a b c d F (t,v)) v := by
  have hJ := continuousOn_rectangleJetV hab hcd hF
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hJ
  have hsec (s : ℝ) (hs : s ∈ Icc c d) : ContinuousOn (fun t => F (t,s)) (Icc a u) :=
    hF.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun t ht => ⟨⟨ht.1,ht.2.trans hu.2⟩,hs⟩)
  have hJsec : ContinuousOn (fun t => rectangleJetV a b c d F (t,v)) (Icc a u) :=
    hJ.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun t ht => ⟨⟨ht.1,ht.2.trans hu.2⟩,⟨hv.1.le,hv.2.le⟩⟩)
  have hmeas : ∀ᶠ s in 𝓝 v,
      AEStronglyMeasurable (fun t => F (t,s)) (volume.restrict (Ioc a u)) := by
    filter_upwards [Ioo_mem_nhds hv.1 hv.2] with s hs
    exact ((hsec s ⟨hs.1.le,hs.2.le⟩).intervalIntegrable_of_Icc hu.1).1.aestronglyMeasurable
  have hbound : ∀ᵐ t ∂(volume.restrict (Ioc a u)), ∀ s ∈ Ioo c d,
      ‖rectangleJetV a b c d F (t,s)‖ ≤ B := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    intro s hs
    exact hB (t,s) ⟨⟨ht.1.le,ht.2.trans hu.2⟩,⟨hs.1.le,hs.2.le⟩⟩
  have hdiff : ∀ᵐ t ∂(volume.restrict (Ioc a u)), ∀ s ∈ Ioo c d,
      HasDerivAt (fun x => F (t,x)) (rectangleJetV a b c d F (t,s)) s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    intro s hs
    exact (hasDerivWithinAt_rectangleJetV hF ⟨ht.1.le,ht.2.trans hu.2⟩
      ⟨hs.1.le,hs.2.le⟩).hasDerivAt (Icc_mem_nhds hs.1 hs.2)
  have hi := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioc a u)) (F := fun s t => F (t,s))
    (F' := fun s t => rectangleJetV a b c d F (t,s)) (bound := fun _ => B)
    (Ioo_mem_nhds hv.1 hv.2) hmeas
    ((hsec v ⟨hv.1.le,hv.2.le⟩).intervalIntegrable_of_Icc hu.1).1
    ((hJsec.intervalIntegrable_of_Icc hu.1).1.aestronglyMeasurable) hbound
    (continuous_const.intervalIntegrable a u).1 hdiff
  simpa only [intervalIntegral.integral_of_le hu.1] using hi.2

/-- The incoming primitive identity gives its outgoing first-jet
integral identity up to both closed parameter endpoints. -/
theorem derivWithin_eq_add_integral_rectangleJetV {a b c d u : ℝ}
    (hab : a < b) (hcd : c < d) {f yi : ℝ → E} {G : ℝ × ℝ → E}
    (hf : ContDiffOn ℝ 1 f (Icc c d)) (hyi : ContDiffOn ℝ 1 yi (Icc c d))
    (hG : ContDiffOn ℝ 1 G (Icc a b ×ˢ Icc c d)) (hu : u ∈ Icc a b)
    (heq : ∀ v ∈ Icc c d, f v = yi v + ∫ t in a..u, G (t, v)) :
    ∀ v ∈ Icc c d, derivWithin f (Icc c d) v = derivWithin yi (Icc c d) v +
      ∫ t in a..u, rectangleJetV a b c d G (t,v) := by
  have hleft := (contDiffOn_one_iff_derivWithin (uniqueDiffOn_Icc hcd)).mp hf |>.2
  have hJ := continuousOn_rectangleJetV hab hcd hG
  have hJs : ContinuousOn (fun p : ℝ × ℝ => rectangleJetV a b c d G (p.2,p.1))
      (Icc c d ×ˢ Icc a b) :=
    hJ.comp continuous_swap.continuousOn (fun p hp => ⟨hp.2,hp.1⟩)
  have hright := ((contDiffOn_one_iff_derivWithin (uniqueDiffOn_Icc hcd)).mp hyi |>.2).add
    (continuousOn_integral_rectangle hab.le hJs hu)
  have hint : EqOn (derivWithin f (Icc c d))
      (fun v => derivWithin yi (Icc c d) v +
        ∫ t in a..u, rectangleJetV a b c d G (t,v)) (Ioo c d) := by
    intro v hv
    have hv' : v ∈ Icc c d := ⟨hv.1.le,hv.2.le⟩
    have hd := (hyi.differentiableOn (by decide) v hv').hasDerivWithinAt.hasDerivAt
      (Icc_mem_nhds hv.1 hv.2)
    have hi := hasDerivAt_integral_rectangleJetV hab hcd hG hu hv
    have hevent : f =ᶠ[𝓝 v] fun s => yi s + ∫ t in a..u, G (t,s) := by
      filter_upwards [Icc_mem_nhds hv.1 hv.2] with s hs
      exact heq s hs
    exact ((hf.differentiableOn (by decide) v hv').hasDerivWithinAt.hasDerivAt
      (Icc_mem_nhds hv.1 hv.2)).unique ((hd.add hi).congr_of_eventuallyEq hevent)
  exact hint.of_subset_closure hleft hright Ioo_subset_Icc_self
    (by rw [closure_Ioo hcd.ne])

/-- Chain rule for the actual incoming rectangle jet of a composed
state source. The source is differentiated only in finite state space. -/
theorem rectangleJetU_comp {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    {F : ℝ × ℝ → E} (hF : ContDiffOn ℝ 1 F (Icc a b ×ˢ Icc c d))
    {φ : E → G} {p : ℝ × ℝ} (hp : p ∈ Icc a b ×ˢ Icc c d)
    (hφ : DifferentiableAt ℝ φ (F p)) :
    rectangleJetU a b c d (φ ∘ F) p = fderiv ℝ φ (F p) (rectangleJetU a b c d F p) := by
  have hd := hφ.hasFDerivAt.comp_hasFDerivWithinAt p
    (hF.differentiableOn (by decide) p hp).hasFDerivWithinAt
  have heq := hd.fderivWithin (((uniqueDiffOn_Icc hab).prod (uniqueDiffOn_Icc hcd)) p hp)
  unfold rectangleJetU
  rw [heq]
  rfl

/-- Chain rule for the actual outgoing rectangle jet of a composed
state source, requiring no second derivatives. -/
theorem rectangleJetV_comp {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    {F : ℝ × ℝ → E} (hF : ContDiffOn ℝ 1 F (Icc a b ×ˢ Icc c d))
    {φ : E → G} {p : ℝ × ℝ} (hp : p ∈ Icc a b ×ˢ Icc c d)
    (hφ : DifferentiableAt ℝ φ (F p)) :
    rectangleJetV a b c d (φ ∘ F) p = fderiv ℝ φ (F p) (rectangleJetV a b c d F p) := by
  have hd := hφ.hasFDerivAt.comp_hasFDerivWithinAt p
    (hF.differentiableOn (by decide) p hp).hasFDerivWithinAt
  have heq := hd.fderivWithin (((uniqueDiffOn_Icc hab).prod (uniqueDiffOn_Icc hcd)) p hp)
  unfold rectangleJetV
  rw [heq]
  rfl

section Product

variable {I O : Type*} [NormedAddCommGroup I] [NormedSpace ℝ I]
  [NormedAddCommGroup O] [NormedSpace ℝ O]

/-- The first transverse equation in internal project record (47), in full-state
jet notation, on every side of the closed rectangle. Its incoming state
jet component is supplied by the incoming characteristic equation. -/
theorem goursat_transverse_jetU_integral_eq {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    {F : ℝ × ℝ → I × O} (hF : ContDiffOn ℝ 1 F (Icc a b ×ˢ Icc c d))
    {xb : ℝ → O} (hxb : ContDiffOn ℝ 1 xb (Icc a b)) {fo : I × O → O}
    (hfo : ∀ p ∈ Icc a b ×ˢ Icc c d, ContDiffAt ℝ 1 fo (F p))
    (hXb : ∀ u ∈ Icc a b, ∀ v ∈ Icc c d,
      (F (u, v)).2 = xb u + ∫ t in c..v, fo (F (u, t)))
    {u v : ℝ} (hu : u ∈ Icc a b) (hv : v ∈ Icc c d) :
    (rectangleJetU a b c d F (u,v)).2 = derivWithin xb (Icc a b) u +
      ∫ t in c..v, fderiv ℝ fo (F (u,t)) (rectangleJetU a b c d F (u,t)) := by
  have hG : ContDiffOn ℝ 1 (fo ∘ F) (Icc a b ×ˢ Icc c d) :=
    fun p hp => (hfo p hp).comp_contDiffWithinAt p (hF p hp)
  have hf : ContDiffOn ℝ 1 (fun s => (F (s,v)).2) (Icc a b) :=
    hF.snd.comp (contDiffOn_id.prodMk contDiffOn_const) (fun s hs => ⟨hs,hv⟩)
  have heq := derivWithin_eq_add_integral_rectangleJetU hab hcd hf hxb hG hv
    (fun s hs => hXb s hs v hv) u hu
  have hsection : HasDerivWithinAt (fun s => (F (s,v)).2)
      (rectangleJetU a b c d F (u,v)).2 (Icc a b) u :=
    (ContinuousLinearMap.snd ℝ I O).hasFDerivAt.comp_hasDerivWithinAt u
      (hasDerivWithinAt_rectangleJetU hF hu hv)
  have hjet := hsection.derivWithin (uniqueDiffOn_Icc hab u hu)
  rw [← hjet, heq]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hv.1] at ht
  have hp : (u,t) ∈ Icc a b ×ˢ Icc c d := ⟨hu,⟨ht.1,ht.2.trans hv.2⟩⟩
  exact rectangleJetU_comp hab hcd hF hp ((hfo (u,t) hp).differentiableAt (by decide))

/-- The second transverse equation in internal project record (47), in full-state
jet notation, on every closed rectangle side. The outgoing state jet
component is supplied by the outgoing characteristic equation. -/
theorem goursat_transverse_jetV_integral_eq {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    {F : ℝ × ℝ → I × O} (hF : ContDiffOn ℝ 1 F (Icc a b ×ˢ Icc c d))
    {yi : ℝ → I} (hyi : ContDiffOn ℝ 1 yi (Icc c d)) {fi : I × O → I}
    (hfi : ∀ p ∈ Icc a b ×ˢ Icc c d, ContDiffAt ℝ 1 fi (F p))
    (hYi : ∀ u ∈ Icc a b, ∀ v ∈ Icc c d,
      (F (u, v)).1 = yi v + ∫ s in a..u, fi (F (s, v)))
    {u v : ℝ} (hu : u ∈ Icc a b) (hv : v ∈ Icc c d) :
    (rectangleJetV a b c d F (u,v)).1 = derivWithin yi (Icc c d) v +
      ∫ s in a..u, fderiv ℝ fi (F (s,v)) (rectangleJetV a b c d F (s,v)) := by
  have hG : ContDiffOn ℝ 1 (fi ∘ F) (Icc a b ×ˢ Icc c d) :=
    fun p hp => (hfi p hp).comp_contDiffWithinAt p (hF p hp)
  have hf : ContDiffOn ℝ 1 (fun t => (F (u,t)).1) (Icc c d) :=
    hF.fst.comp (contDiffOn_const.prodMk contDiffOn_id) (fun t ht => ⟨hu,ht⟩)
  have heq := derivWithin_eq_add_integral_rectangleJetV hab hcd hf hyi hG hu
    (fun t ht => hYi u hu t ht) v hv
  have hsection : HasDerivWithinAt (fun t => (F (u,t)).1)
      (rectangleJetV a b c d F (u,v)).1 (Icc c d) v :=
    (ContinuousLinearMap.fst ℝ I O).hasFDerivAt.comp_hasDerivWithinAt v
      (hasDerivWithinAt_rectangleJetV hF hu hv)
  have hjet := hsection.derivWithin (uniqueDiffOn_Icc hcd v hv)
  rw [← hjet, heq]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le hu.1] at hs
  have hp : (s,v) ∈ Icc a b ×ˢ Icc c d := ⟨⟨hs.1,hs.2.trans hu.2⟩,hv⟩
  exact rectangleJetV_comp hab hcd hF hp ((hfi (s,v) hp).differentiableAt (by decide))

end Product

end EmcsfAcExtension.Local
