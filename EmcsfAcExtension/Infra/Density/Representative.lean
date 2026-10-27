module

public import EmcsfAcExtension.Infra.Density.ParamIntegral
public import EmcsfAcExtension.Infra.LinearTransport
import EmcsfAcExtension.Infra.Null.Parametric

/-!
# Fixed initial densities

A transported density is evaluated using its prescribed initial label density.
Sectionwise equality and continuity in the incoming variable give one common
null set of labels. These abstract results do not identify any physical field.
-/

public section

open Set MeasureTheory Filter TopologicalSpace
open scoped Topology

namespace EmcsfAcExtension.Global.Density

/-- [internal] A continuous multiplier and remainder acting on the fixed initial
label density. The values of `y₀` on its exceptional set are retained explicitly. -/
@[expose] noncomputable def fixedDensity (P R : ℝ → ℝ → ℂ) (y₀ : ℝ → ℂ) (u v : ℝ) : ℂ :=
  P u v * y₀ v + R u v

/-- [internal] Borel initial data and Borel factors give a jointly Borel selected
density. This statement makes no continuity claim about the initial density. -/
theorem measurable_fixedDensity {P R : ℝ → ℝ → ℂ} {y₀ : ℝ → ℂ}
    (hP : Measurable P.uncurry) (hR : Measurable R.uncurry) (hy₀ : Measurable y₀) :
    Measurable (fixedDensity P R y₀).uncurry :=
  (hP.mul (hy₀.comp measurable_snd)).add hR

/-- [internal] With an arbitrary L¹ initial representative, the selected density
is jointly a.e. strongly measurable on the rectangle. Borel initial values are
not required for this assertion. -/
theorem aestronglyMeasurable_fixedDensity {P R : ℝ → ℝ → ℂ} {y₀ : ℝ → ℂ}
    {a b c d : ℝ} (hcd : c ≤ d)
    (hP : ContinuousOn P.uncurry (Icc a b ×ˢ Icc c d))
    (hR : ContinuousOn R.uncurry (Icc a b ×ˢ Icc c d))
    (hy₀ : IntervalIntegrable y₀ volume c d) :
    AEStronglyMeasurable (fixedDensity P R y₀).uncurry
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) := by
  have hPr : AEStronglyMeasurable P.uncurry
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) := by
    rw [Measure.prod_restrict]
    exact hP.aestronglyMeasurable (measurableSet_Icc.prod measurableSet_Icc)
  have hRr : AEStronglyMeasurable R.uncurry
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) := by
    rw [Measure.prod_restrict]
    exact hR.aestronglyMeasurable (measurableSet_Icc.prod measurableSet_Icc)
  have hy : AEStronglyMeasurable y₀ (volume.restrict (Icc c d)) :=
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hcd).mp hy₀).aestronglyMeasurable
  exact (hPr.mul (hy.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)).add hRr

/-- [internal] The selected density is integrable on every outgoing row when
the multiplier and remainder are continuous and the fixed initial density is L¹. -/
theorem intervalIntegrable_fixedDensity {P R : ℝ → ℝ → ℂ} {y₀ : ℝ → ℂ}
    {a b c d u : ℝ} (hcd : c ≤ d) (hu : u ∈ Icc a b)
    (hP : ContinuousOn P.uncurry (Icc a b ×ˢ Icc c d))
    (hR : ContinuousOn R.uncurry (Icc a b ×ˢ Icc c d))
    (hy₀ : IntervalIntegrable y₀ volume c d) :
    IntervalIntegrable (fixedDensity P R y₀ u) volume c d := by
  have hPu : ContinuousOn (P u) (uIcc c d) := by
    rw [uIcc_of_le hcd]
    exact hP.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun v hv => ⟨hu, hv⟩)
  have hRu : ContinuousOn (R u) (uIcc c d) := by
    rw [uIcc_of_le hcd]
    exact hR.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun v hv => ⟨hu, hv⟩)
  exact (hy₀.continuousOn_mul hPu).add hRu.intervalIntegrable

/-- [internal] A compact rectangle gives one majorant constant depending only
on the two factors and the rectangle, uniformly in the initial density and both
coordinates. The initial density is only required to be L¹ in applications. -/
theorem exists_fixedDensity_bound {P R : ℝ → ℝ → ℂ} {a b c d : ℝ}
    (hP : ContinuousOn P.uncurry (Icc a b ×ˢ Icc c d))
    (hR : ContinuousOn R.uncurry (Icc a b ×ˢ Icc c d)) :
    ∃ C > 0, ∀ y₀ : ℝ → ℂ, ∀ u ∈ Icc a b, ∀ v ∈ Icc c d,
      ‖fixedDensity P R y₀ u v‖ ≤ C * (‖y₀ v‖ + 1) := by
  obtain ⟨CP, hCP⟩ := (isCompact_Icc.prod isCompact_Icc).bddAbove_image hP.norm
  obtain ⟨CR, hCR⟩ := (isCompact_Icc.prod isCompact_Icc).bddAbove_image hR.norm
  let C := max 1 (max CP CR)
  have hPC : CP ≤ C := (le_max_left CP CR).trans (le_max_right 1 _)
  have hRC : CR ≤ C := (le_max_right CP CR).trans (le_max_right 1 _)
  refine ⟨C, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro y₀ u hu v hv
  calc
    ‖fixedDensity P R y₀ u v‖ ≤ ‖P u v * y₀ v‖ + ‖R u v‖ := norm_add_le _ _
    _ = ‖P u v‖ * ‖y₀ v‖ + ‖R u v‖ := by rw [norm_mul]
    _ ≤ C * ‖y₀ v‖ + C :=
      add_le_add (mul_le_mul_of_nonneg_right ((hCP ⟨(u, v), ⟨hu, hv⟩, rfl⟩).trans hPC)
        (norm_nonneg _)) ((hCR ⟨(u, v), ⟨hu, hv⟩, rfl⟩).trans hRC)
    _ = C * (‖y₀ v‖ + 1) := by ring

/-- [internal] The outgoing primitive has the selected density as derivative
for every incoming parameter outside one common null set of labels. The two
factors are continuous on the rectangle; the initial density is only L¹. -/
theorem ae_forall_hasDerivAt_fixedDensity_primitive
    {P R : ℝ → ℝ → ℂ} {y₀ : ℝ → ℂ} {a b c d : ℝ} (hcd : c ≤ d)
    (hP : ContinuousOn P.uncurry (Icc a b ×ˢ Icc c d))
    (hR : ContinuousOn R.uncurry (Icc a b ×ˢ Icc c d))
    (hy₀ : IntervalIntegrable y₀ volume c d) :
    ∀ᵐ v ∂volume.restrict (Icc c d), ∀ u ∈ Icc a b,
      HasDerivAt (fun x => ∫ s in c..x, fixedDensity P R y₀ u s)
        (fixedDensity P R y₀ u v) v := by
  have hne (x : ℝ) : ∀ᵐ y ∂volume.restrict (Icc c d), y ≠ x := by
    apply ae_restrict_of_ae
    simp [ae_iff]
  filter_upwards [ae_forall_continuous_weight_hasDerivAt hcd hy₀,
    ae_restrict_mem measurableSet_Icc, hne c, hne d] with v hv hvm hvc hvd u hu
  have hvi : v ∈ Ioo c d := ⟨lt_of_le_of_ne hvm.1 (Ne.symm hvc),
    lt_of_le_of_ne hvm.2 hvd⟩
  have hPu : ContinuousOn (P u) (Icc c d) :=
    hP.comp (continuous_const.prodMk continuous_id).continuousOn (fun s hs => ⟨hu, hs⟩)
  have hRu : ContinuousOn (R u) (Icc c d) :=
    hR.comp (continuous_const.prodMk continuous_id).continuousOn (fun s hs => ⟨hu, hs⟩)
  have hPy : IntervalIntegrable (fun s => P u s * y₀ s) volume c d :=
    hy₀.continuousOn_mul (by rwa [uIcc_of_le hcd])
  have hRi : IntervalIntegrable (R u) volume c d :=
    hRu.intervalIntegrable_of_Icc hcd
  have hsub : uIcc c v ⊆ uIcc c d := by
    apply uIcc_subset_uIcc left_mem_uIcc
    rwa [uIcc_of_le hcd]
  have hn := Icc_mem_nhds hvi.1 hvi.2
  have hmeas : AEStronglyMeasurable (R u) (volume.restrict (Icc c d)) :=
    hRu.aestronglyMeasurable measurableSet_Icc
  have hdR := intervalIntegral.integral_hasDerivAt_right (hRi.mono_set hsub)
    ⟨Icc c d, hn, hmeas⟩
    (hRu.continuousAt hn)
  have hd := (hv (P u) hPu).add hdR
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hvi.1 hvi.2] with x hx
  have hsubx : uIcc c x ⊆ uIcc c d := by
    apply uIcc_subset_uIcc left_mem_uIcc
    rw [uIcc_of_le hcd]
    exact Ioo_subset_Icc_self hx
  exact intervalIntegral.integral_add (hPy.mono_set hsubx) (hRi.mono_set hsubx)

/-- [internal] An everywhere primitive identity identifies the outgoing
derivative on every row with the same fixed initial density representative.
The exceptional label set precedes the quantifier over incoming times. -/
theorem ae_forall_hasDerivAt_of_fixedDensity_representation
    {f P R : ℝ → ℝ → ℂ} {y₀ : ℝ → ℂ} {a b c d : ℝ} (hcd : c ≤ d)
    (hP : ContinuousOn P.uncurry (Icc a b ×ˢ Icc c d))
    (hR : ContinuousOn R.uncurry (Icc a b ×ˢ Icc c d))
    (hy₀ : IntervalIntegrable y₀ volume c d)
    (hrep : ∀ u ∈ Icc a b, ∀ v ∈ Icc c d,
      f u v = f u c + ∫ s in c..v, fixedDensity P R y₀ u s) :
    ∀ᵐ v ∂volume.restrict (Icc c d), ∀ u ∈ Icc a b,
      HasDerivAt (f u) (fixedDensity P R y₀ u v) v := by
  have hne (x : ℝ) : ∀ᵐ y ∂volume.restrict (Icc c d), y ≠ x := by
    apply ae_restrict_of_ae
    simp [ae_iff]
  filter_upwards [ae_forall_hasDerivAt_fixedDensity_primitive hcd hP hR hy₀,
    ae_restrict_mem measurableSet_Icc, hne c, hne d] with v hv hvm hvc hvd u hu
  have hd := (hv u hu).const_add (f u c)
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds (lt_of_le_of_ne hvm.1 (Ne.symm hvc))
    (lt_of_le_of_ne hvm.2 hvd)] with x hx
  exact hrep u hu x (Ioo_subset_Icc_self hx)

/-- [internal] The complex variation-of-constants expression based at a fixed row. -/
@[expose] noncomputable def transportDensity (c F : ℝ → ℝ → ℂ) (y₀ : ℝ → ℂ)
    (a u v : ℝ) : ℂ :=
  Complex.exp (∫ s in a..u, c s v) *
    (y₀ v + ∫ s in a..u, Complex.exp (-(∫ t in a..s, c t v)) * F s v)

/-- [internal] The selected incoming density has the prescribed initial value
at every label, including labels in the exceptional set. -/
@[simp] theorem transportDensity_initial (c F : ℝ → ℝ → ℂ) (y₀ : ℝ → ℂ)
    (a v : ℝ) : transportDensity c F y₀ a a v = y₀ v := by
  simp [transportDensity]

/-- [internal] Integrable coefficients and forcing make the selected incoming
representative AC, for every label at which those two sections are integrable. -/
theorem absolutelyContinuousOnInterval_transportDensity
    {c F : ℝ → ℝ → ℂ} (y₀ : ℝ → ℂ) {a b v : ℝ}
    (hc : IntervalIntegrable (fun s => c s v) volume a b)
    (hF : IntervalIntegrable (fun s => F s v) volume a b) :
    AbsolutelyContinuousOnInterval (fun u => transportDensity c F y₀ a u v) a b := by
  have hC := hc.absolutelyContinuousOnInterval_intervalIntegral_complex left_mem_uIcc
  have hw := hC.neg.cexp
  have hq := hF.continuousOn_mul hw.continuousOn
  exact hC.cexp.mul_normed_ring
    (((LipschitzWith.const (y₀ v)).lipschitzOnWith.absolutelyContinuousOnInterval).add
      (hq.absolutelyContinuousOnInterval_intervalIntegral_complex left_mem_uIcc))

/-- [internal] The incoming derivative of the selected representative is the
linear transport equation a.e.; its initial density is never differentiated. -/
theorem ae_hasDerivAt_transportDensity {c F : ℝ → ℝ → ℂ} (y₀ : ℝ → ℂ)
    {a b v : ℝ}
    (hc : IntervalIntegrable (fun s => c s v) volume a b)
    (hF : IntervalIntegrable (fun s => F s v) volume a b) :
    ∀ᵐ u, u ∈ uIcc a b → HasDerivAt (fun t => transportDensity c F y₀ a t v)
      (c u v * transportDensity c F y₀ a u v + F u v) u := by
  let C : ℝ → ℂ := fun u => ∫ s in a..u, c s v
  have hC := hc.absolutelyContinuousOnInterval_intervalIntegral_complex left_mem_uIcc
  have hq := hF.continuousOn_mul hC.neg.cexp.continuousOn
  filter_upwards [hc.ae_hasDerivAt_integral, hq.ae_hasDerivAt_integral] with u hcu hqu hu
  have hdC : HasDerivAt C (c u v) u := hcu hu a left_mem_uIcc
  have hdq := (hqu hu a left_mem_uIcc).const_add (y₀ v)
  have hd := hdC.cexp.mul hdq
  have he : Complex.exp (C u) * Complex.exp (-C u) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  apply hd.congr_deriv
  change Complex.exp (C u) * c u v *
      (y₀ v + ∫ s in a..u, Complex.exp (-C s) * F s v) +
      Complex.exp (C u) * (Complex.exp (-C u) * F u v) = _
  rw [← mul_assoc (Complex.exp (C u)) (Complex.exp (-C u)), he, one_mul]
  dsimp only [transportDensity, C]
  ring

/-- [internal] The incoming primitive of a jointly continuous function is
jointly continuous, with the first coordinate as the integration parameter. -/
theorem continuous_incoming_primitive {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {c : ℝ → ℝ → E} (hc : Continuous c.uncurry) (a : ℝ) :
    Continuous (fun p : ℝ × ℝ => ∫ s in a..p.1, c s p.2) := by
  have hswap : Continuous (Function.uncurry (fun v s => c s v)) := hc.comp continuous_swap
  exact (intervalIntegral.continuous_parametric_primitive_of_continuous
    (f := fun v s => c s v) (a₀ := a) (μ := volume) hswap).comp continuous_swap

/-- [internal] Variation of constants splits into a jointly continuous
multiplier and remainder. The initial label density is arbitrary. -/
theorem exists_continuous_transport_factors {c F : ℝ → ℝ → ℂ}
    (hc : Continuous c.uncurry) (hF : Continuous F.uncurry) (a : ℝ) :
    ∃ P R : ℝ → ℝ → ℂ, Continuous P.uncurry ∧ Continuous R.uncurry ∧
      ∀ y₀ u v, transportDensity c F y₀ a u v = fixedDensity P R y₀ u v := by
  let C : ℝ → ℝ → ℂ := fun u v => ∫ s in a..u, c s v
  have hC : Continuous C.uncurry := continuous_incoming_primitive hc a
  let P : ℝ → ℝ → ℂ := fun u v => Complex.exp (C u v)
  let q : ℝ → ℝ → ℂ := fun u v => Complex.exp (-C u v) * F u v
  have hP : Continuous P.uncurry := Complex.continuous_exp.comp hC
  have hq : Continuous q.uncurry := (Complex.continuous_exp.comp hC.neg).mul hF
  let R : ℝ → ℝ → ℂ := fun u v => P u v * ∫ s in a..u, q s v
  refine ⟨P, R, hP, hP.mul (continuous_incoming_primitive hq a), ?_⟩
  intro y₀ u v
  dsimp only [transportDensity, fixedDensity, P, R, q, C]
  ring

/-- [internal] The selected transport density depends only on the coefficient
and forcing on the visible rectangle. No values outside it enter the formula. -/
theorem transportDensity_congr_on_rectangle {c₁ c₂ F₁ F₂ : ℝ → ℝ → ℂ}
    (y₀ : ℝ → ℂ) {a b c d u v : ℝ}
    (hc : EqOn c₁.uncurry c₂.uncurry (Icc a b ×ˢ Icc c d))
    (hF : EqOn F₁.uncurry F₂.uncurry (Icc a b ×ˢ Icc c d))
    (hu : u ∈ Icc a b) (hv : v ∈ Icc c d) :
    transportDensity c₁ F₁ y₀ a u v = transportDensity c₂ F₂ y₀ a u v := by
  have hC (x : ℝ) (hx : x ∈ Icc a b) :
      (∫ s in a..x, c₁ s v) = ∫ s in a..x, c₂ s v := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hx.1] at hs
    exact hc (show (s, v) ∈ Icc a b ×ˢ Icc c d from
      ⟨⟨hs.1, hs.2.trans hx.2⟩, hv⟩)
  unfold transportDensity
  rw [hC u hu]
  congr 2
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le hu.1] at hs
  have hsm : s ∈ Icc a b := ⟨hs.1, hs.2.trans hu.2⟩
  change Complex.exp (-∫ t in a..s, c₁ t v) * F₁ s v =
    Complex.exp (-∫ t in a..s, c₂ t v) * F₂ s v
  have hFs : F₁ s v = F₂ s v :=
    hF (show (s, v) ∈ Icc a b ×ˢ Icc c d from ⟨hsm, hv⟩)
  rw [hC s hsm, hFs]

/-- [internal] Local continuous coefficients and forcing give continuous
multiplier and remainder on a closed rectangle. A continuous clamped extension
is constructed in the proof; no outside regularity hypothesis is imposed. -/
theorem exists_continuousOn_transport_factors {c F : ℝ → ℝ → ℂ} {a b l r : ℝ}
    (hab : a ≤ b) (hlr : l ≤ r)
    (hc : ContinuousOn c.uncurry (Icc a b ×ˢ Icc l r))
    (hF : ContinuousOn F.uncurry (Icc a b ×ˢ Icc l r)) :
    ∃ P R : ℝ → ℝ → ℂ,
      ContinuousOn P.uncurry (Icc a b ×ˢ Icc l r) ∧
      ContinuousOn R.uncurry (Icc a b ×ˢ Icc l r) ∧
      ∀ y₀ u, u ∈ Icc a b → ∀ v ∈ Icc l r,
        transportDensity c F y₀ a u v = fixedDensity P R y₀ u v := by
  let π : ℝ × ℝ → ℝ × ℝ := fun p =>
    (min (max a p.1) b, min (max l p.2) r)
  have hπ : Continuous π := by fun_prop
  have hπmem (p : ℝ × ℝ) : π p ∈ Icc a b ×ˢ Icc l r :=
    ⟨⟨le_min (le_max_left _ _) hab, min_le_right _ _⟩,
      ⟨le_min (le_max_left _ _) hlr, min_le_right _ _⟩⟩
  have hπid {p : ℝ × ℝ} (hp : p ∈ Icc a b ×ˢ Icc l r) : π p = p := by
    dsimp only [π]
    rw [max_eq_right hp.1.1, min_eq_left hp.1.2,
      max_eq_right hp.2.1, min_eq_left hp.2.2]
  let C : ℝ → ℝ → ℂ := fun u v => c.uncurry (π (u, v))
  let H : ℝ → ℝ → ℂ := fun u v => F.uncurry (π (u, v))
  have hC : Continuous C.uncurry := hc.comp_continuous hπ hπmem
  have hH : Continuous H.uncurry := hF.comp_continuous hπ hπmem
  obtain ⟨P, R, hP, hR, heq⟩ := exists_continuous_transport_factors hC hH a
  refine ⟨P, R, hP.continuousOn, hR.continuousOn, ?_⟩
  intro y₀ u hu v hv
  apply Eq.trans (transportDensity_congr_on_rectangle y₀
    (c₂ := C) (F₂ := H) ?_ ?_ hu hv) (heq y₀ u v)
  · intro p hp
    change c.uncurry p = c.uncurry (π p)
    rw [hπid hp]
  · intro p hp
    change F.uncurry p = F.uncurry (π p)
    rw [hπid hp]

/-- [internal] Continuous local coefficients and forcing give an incoming AC
representative satisfying the ODE a.e. for every label. In particular the weaker
assertion for almost every label holds for any L¹ initial density. -/
theorem forall_transportDensity_ac_and_ae_deriv {c F : ℝ → ℝ → ℂ}
    (y₀ : ℝ → ℂ) {a b l r : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn c.uncurry (Icc a b ×ˢ Icc l r))
    (hF : ContinuousOn F.uncurry (Icc a b ×ˢ Icc l r)) :
    ∀ v ∈ Icc l r,
      AbsolutelyContinuousOnInterval (fun u => transportDensity c F y₀ a u v) a b ∧
      ∀ᵐ u ∂volume.restrict (Icc a b),
        HasDerivAt (fun t => transportDensity c F y₀ a t v)
          (c u v * transportDensity c F y₀ a u v + F u v) u := by
  intro v hv
  have hcv : IntervalIntegrable (fun u => c u v) volume a b :=
    (hc.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun u hu => ⟨hu, hv⟩)).intervalIntegrable_of_Icc hab
  have hFv : IntervalIntegrable (fun u => F u v) volume a b :=
    (hF.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun u hu => ⟨hu, hv⟩)).intervalIntegrable_of_Icc hab
  refine ⟨absolutelyContinuousOnInterval_transportDensity y₀ hcv hFv, ?_⟩
  apply (ae_restrict_iff' measurableSet_Icc).mpr
  filter_upwards [ae_hasDerivAt_transportDensity y₀ hcv hFv] with u hu hum
  exact hu (by rwa [uIcc_of_le hab])

/-- [internal] Every AC solution of the sectional linear ODE is the selected
transport density, at every time in the interval. The initial value is fixed. -/
theorem eq_transportDensity_of_ac_deriv_eq {c F : ℝ → ℝ → ℂ}
    {y : ℝ → ℂ} {y₀ : ℝ → ℂ} {a b v : ℝ} (hab : a ≤ b)
    (hy : AbsolutelyContinuousOnInterval y a b)
    (hc : IntervalIntegrable (fun s => c s v) volume a b)
    (hF : IntervalIntegrable (fun s => F s v) volume a b)
    (heq : ∀ᵐ u ∂volume.restrict (Icc a b), deriv y u = c u v * y u + F u v)
    (hinit : y a = y₀ v) :
    ∀ u ∈ Icc a b, y u = transportDensity c F y₀ a u v := by
  intro u hu
  simpa only [transportDensity, hinit] using
    EmcsfAcExtension.eq_integratingFactor_of_ac_deriv_eq_complex hab hy hc hF heq u hu

end EmcsfAcExtension.Global.Density
