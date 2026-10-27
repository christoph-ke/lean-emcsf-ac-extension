module

public import EmcsfAcExtension.Infra.AC.Primitive
public import EmcsfAcExtension.Infra.Triangle
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Parameter integrals with an integrable incoming density

All exceptional sets in the sectional assertions are sets of labels. In particular,
the incoming primitive is absolutely continuous on the whole parameter interval
outside one label-null set, rather than on unrelated sets for different times.
The statements are independent of the field equations.
-/

public section

open Set MeasureTheory Filter Asymptotics
open scoped Topology

namespace EmcsfAcExtension.Global.Density

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- [internal] A jointly strongly measurable density has a jointly strongly
measurable incoming primitive, including both orientations of the interval.
Integrability is not needed for this measurability assertion. -/
theorem stronglyMeasurable_incoming_primitive {H : ℝ → ℝ → E}
    (hH : StronglyMeasurable H.uncurry) (a : ℝ) :
    StronglyMeasurable (fun p : ℝ × ℝ => ∫ s in a..p.1, H s p.2) := by
  classical
  let L : Set ((ℝ × ℝ) × ℝ) := {q | a < q.2 ∧ q.2 ≤ q.1.1}
  let R : Set ((ℝ × ℝ) × ℝ) := {q | q.1.1 < q.2 ∧ q.2 ≤ a}
  let K : (ℝ × ℝ) × ℝ → E := fun q => H q.2 q.1.2
  have hK : StronglyMeasurable K := hH.comp_measurable
    (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
  have hL : MeasurableSet L :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (measurable_fst.comp measurable_fst))
  have hR : MeasurableSet R :=
    (measurableSet_lt (measurable_fst.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)
  have hmeas : StronglyMeasurable (fun p : ℝ × ℝ =>
      (∫ s, L.indicator K (p, s)) - ∫ s, R.indicator K (p, s)) :=
    (hK.indicator hL).integral_prod_right'.sub (hK.indicator hR).integral_prod_right'
  have hleft (p : ℝ × ℝ) : (fun s => L.indicator K (p, s)) =
      (Ioc a p.1).indicator (fun s => H s p.2) := by
    funext s
    rfl
  have hright (p : ℝ × ℝ) : (fun s => R.indicator K (p, s)) =
      (Ioc p.1 a).indicator (fun s => H s p.2) := by
    funext s
    rfl
  convert hmeas using 1
  funext p
  simp only [hleft, hright, integral_indicator measurableSet_Ioc]
  rcases le_total a p.1 with hap | hpa
  · simp only [intervalIntegral.integral_of_le hap, Ioc_eq_empty_of_le hap,
      Measure.restrict_empty, integral_zero_measure, sub_zero]
  · simp only [intervalIntegral.integral_of_ge hpa, Ioc_eq_empty_of_le hpa,
      Measure.restrict_empty, integral_zero_measure, zero_sub]

omit [CompleteSpace E] in
/-- [internal] Rectangle Fubini for oriented primitives, requiring integrability only on the
rectangle swept out by the displayed endpoints. -/
theorem integral_integral_swap_rectangle {H : ℝ → ℝ → E} {a b c d : ℝ}
    (hH : IntegrableOn H.uncurry (uIoc a b ×ˢ uIoc c d)) :
    (∫ u in a..b, ∫ v in c..d, H u v) =
      ∫ v in c..d, ∫ u in a..b, H u v :=
  intervalIntegral_intervalIntegral_swap hH

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- [internal] One label-null set suffices for integrability of every anchored incoming
subinterval of a rectangle-integrable density. -/
theorem ae_forall_intervalIntegrable_incoming {H : ℝ → ℝ → E} {a b c d : ℝ}
    (hab : a ≤ b)
    (hH : Integrable H.uncurry
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d)))) :
    ∀ᵐ v ∂volume.restrict (Icc c d), ∀ u ∈ Icc a b,
      IntervalIntegrable (fun s => H s v) volume a u := by
  filter_upwards [hH.prod_left_ae] with v hv u hu
  have hi : IntervalIntegrable (fun s => H s v) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hv
  apply hi.mono_set
  rw [uIcc_of_le hu.1, uIcc_of_le hab]
  exact Icc_subset_Icc le_rfl hu.2

omit [CompleteSpace E] in
/-- [internal] The integral representation selects an incoming AC representative on one
common full-measure set of labels. No regularity is required of the initial values. -/
theorem ae_absolutelyContinuousOnInterval_incoming_primitive
    {H : ℝ → ℝ → E} (y₀ : ℝ → E) {a b c d : ℝ} (hab : a ≤ b)
    (hH : Integrable H.uncurry
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d)))) :
    ∀ᵐ v ∂volume.restrict (Icc c d),
      AbsolutelyContinuousOnInterval
        (fun u => y₀ v + ∫ s in a..u, H s v) a b := by
  filter_upwards [ae_forall_intervalIntegrable_incoming hab hH] with v hv
  exact ((LipschitzWith.const (y₀ v)).lipschitzOnWith.absolutelyContinuousOnInterval).add
    ((hv b ⟨hab, le_rfl⟩).absolutelyContinuousOnInterval_intervalIntegral_normed
      left_mem_uIcc)

/-- [internal] On the same incoming sections the specified density is the derivative a.e.
The order of quantifiers is label first, then incoming time. -/
theorem ae_ae_hasDerivAt_incoming_primitive {H : ℝ → ℝ → E} (y₀ : ℝ → E)
    {a b c d : ℝ} (hab : a ≤ b)
    (hH : Integrable H.uncurry
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d)))) :
    ∀ᵐ v ∂volume.restrict (Icc c d), ∀ᵐ u ∂volume.restrict (Icc a b),
      HasDerivAt (fun t => y₀ v + ∫ s in a..t, H s v) (H u v) u := by
  filter_upwards [ae_forall_intervalIntegrable_incoming hab hH] with v hv
  apply (ae_restrict_iff' measurableSet_Icc).mpr
  filter_upwards [(hv b ⟨hab, le_rfl⟩).ae_hasDerivAt_integral] with u hu humem
  simpa using (hu (by rwa [uIcc_of_le hab]) a left_mem_uIcc).const_add (y₀ v)

omit [CompleteSpace E] in
/-- [internal] Fubini turns the incoming integral representation into an exact
representation of its parameter integral. It holds at every incoming time,
including both endpoints; the hypothesis is only rectangle integrability. -/
theorem integral_incoming_primitive_swap {H : ℝ → ℝ → E} {y₀ : ℝ → E}
    {a b c d : ℝ}
    (hH : Integrable H.uncurry
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))))
    (hy₀ : IntegrableOn y₀ (Icc c d)) {u : ℝ} (hu : u ∈ Icc a b) :
    (∫ v in Icc c d, y₀ v + ∫ s in a..u, H s v) =
      (∫ v in Icc c d, y₀ v) + ∫ s in a..u, ∫ v in Icc c d, H s v := by
  have hsub : uIoc a u ⊆ Icc a b := by
    rw [uIoc_of_le hu.1]
    intro s hs
    exact ⟨hs.1.le, hs.2.trans hu.2⟩
  have hi : Integrable H.uncurry
      ((volume.restrict (uIoc a u)).prod (volume.restrict (Icc c d))) :=
    hH.mono_measure (Measure.prod_mono (Measure.restrict_mono hsub le_rfl) le_rfl)
  have hint : Integrable (fun v => ∫ s in a..u, H s v) (volume.restrict (Icc c d)) := by
    simpa only [Function.uncurry, intervalIntegral.integral_of_le hu.1, uIoc_of_le hu.1] using
      hi.integral_prod_right
  rw [integral_add hy₀ hint, intervalIntegral_integral_swap hi]

/-- [internal] Weak incoming differentiation of a parameter integral from the
integral representation of its density. Each fixed label interval has an AC
parameter integral and the expected a.e. derivative, with no pointwise incoming
derivative hypothesis on `g`. -/
theorem absolutelyContinuousOnInterval_parameterIntegral_of_representation
    {g H : ℝ → ℝ → E} {y₀ : ℝ → E} {a b c d : ℝ} (hab : a ≤ b)
    (hH : Integrable H.uncurry
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))))
    (hy₀ : IntegrableOn y₀ (Icc c d))
    (hrep : ∀ u ∈ Icc a b, g u =ᵐ[volume.restrict (Icc c d)]
      (fun v => y₀ v + ∫ s in a..u, H s v)) :
    AbsolutelyContinuousOnInterval (fun u => ∫ v in Icc c d, g u v) a b ∧
      ∀ᵐ u ∂volume.restrict (Icc a b),
        HasDerivAt (fun t => ∫ v in Icc c d, g t v) (∫ v in Icc c d, H u v) u := by
  let G : ℝ → E := fun u => ∫ v in Icc c d, H u v
  have hG : IntervalIntegrable G volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hH.integral_prod_left
  let z : ℝ → E := fun u => (∫ v in Icc c d, y₀ v) + ∫ s in a..u, G s
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => ∫ v in Icc c d, y₀ v) a b :=
    (LipschitzWith.const _).lipschitzOnWith.absolutelyContinuousOnInterval
  have hz : AbsolutelyContinuousOnInterval z a b :=
    hconst.add (hG.absolutelyContinuousOnInterval_intervalIntegral_normed left_mem_uIcc)
  have heq : EqOn (fun u => ∫ v in Icc c d, g u v) z (Icc a b) := by
    intro u hu
    exact (integral_congr_ae (hrep u hu)).trans (integral_incoming_primitive_swap hH hy₀ hu)
  refine ⟨hz.congr (fun u hu => (heq (by rwa [uIcc_of_le hab] at hu)).symm), ?_⟩
  apply (ae_restrict_iff' measurableSet_Icc).mpr
  have hne (x : ℝ) : ∀ᵐ y : ℝ, y ≠ x := by simp [ae_iff]
  filter_upwards [hG.ae_hasDerivAt_integral, hne a, hne b] with u hu hua hub humem
  have hui : u ∈ Ioo a b := ⟨lt_of_le_of_ne humem.1 (Ne.symm hua),
    lt_of_le_of_ne humem.2 hub⟩
  have hd : HasDerivAt z (G u) u := by
    simpa only [z] using (hu (by rwa [uIcc_of_le hab]) a left_mem_uIcc).const_add
      (∫ v in Icc c d, y₀ v)
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hui.1 hui.2] with t ht
  exact heq (Ioo_subset_Icc_self ht)

private theorem hasDerivAt_weighted_primitive {y P : ℝ → ℂ} {c d v : ℝ}
    (hy : IntervalIntegrable y volume c d) (hP : ContinuousOn P (uIcc c d))
    (hv : v ∈ Ioo c d)
    (hdy : HasDerivAt (fun x => ∫ s in c..x, y s) (y v) v)
    (hdn : HasDerivAt (fun x => ∫ s in c..x, ‖y s‖) ‖y v‖ v) :
    HasDerivAt (fun x => ∫ s in c..x, P s * y s) (P v * y v) v := by
  let A : ℝ → ℂ := fun x => ∫ s in c..x, P s * y s
  let Y : ℝ → ℂ := fun x => ∫ s in c..x, y s
  let N : ℝ → ℝ := fun x => ∫ s in c..x, ‖y s‖
  let z : ℝ → ℂ := fun x => A x - P v * Y x
  have hcd : c ≤ d := hv.1.le.trans hv.2.le
  have hvm : v ∈ uIcc c d := by rw [uIcc_of_le hcd]; exact Ioo_subset_Icc_self hv
  have hPy : IntervalIntegrable (fun s => P s * y s) volume c d :=
    hy.continuousOn_mul hP
  have hPv : ContinuousAt P v := hP.continuousAt (by
    rw [uIcc_of_le hcd]; exact Icc_mem_nhds hv.1 hv.2)
  have hsmall : (fun x => z x - z v) =o[𝓝 v] (fun x => N x - N v) := by
    apply Asymptotics.IsLittleO.of_bound
    intro ε hε
    obtain ⟨δ, hδ, hδP⟩ := Metric.continuousAt_iff.mp hPv ε hε
    filter_upwards [Metric.ball_mem_nhds v hδ, Ioo_mem_nhds hv.1 hv.2] with x hx hxi
    have hxm : x ∈ uIcc c d := by rw [uIcc_of_le hcd]; exact Ioo_subset_Icc_self hxi
    have hsub : uIcc v x ⊆ uIcc c d := uIcc_subset_uIcc hvm hxm
    have hxc : uIcc c x ⊆ uIcc c d := uIcc_subset_uIcc left_mem_uIcc hxm
    have hvc : uIcc c v ⊆ uIcc c d := uIcc_subset_uIcc left_mem_uIcc hvm
    have hres : z x - z v = ∫ s in v..x, (P s - P v) * y s := by
      have hi₁ := hPy.mono_set hsub
      have hi₂ := (hy.mono_set hsub).const_mul (P v)
      simp only [sub_mul]
      rw [intervalIntegral.integral_sub hi₁ hi₂, intervalIntegral.integral_const_mul]
      dsimp only [z, A, Y]
      rw [← intervalIntegral.integral_interval_sub_left (hPy.mono_set hxc) (hPy.mono_set hvc),
        ← intervalIntegral.integral_interval_sub_left (hy.mono_set hxc) (hy.mono_set hvc)]
      ring
    rw [hres]
    have hloc : ∀ s ∈ uIcc v x, ‖P s - P v‖ ≤ ε := by
      intro s hs
      apply le_of_lt
      rw [← dist_eq_norm]
      apply hδP
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hx
      rw [Real.dist_eq, abs_lt]
      rcases le_total v x with hvx | hxv
      · rw [uIcc_of_le hvx] at hs
        constructor <;> linarith [hs.1, hs.2]
      · rw [uIcc_of_ge hxv] at hs
        constructor <;> linarith [hs.1, hs.2]
    have hi : ‖∫ s in v..x, (P s - P v) * y s‖ ≤
        |∫ s in v..x, ε * ‖y s‖| :=
      intervalIntegral.norm_integral_le_abs_of_norm_le
        ((ae_restrict_iff' measurableSet_uIoc).mpr (ae_of_all _ fun s hs => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hloc s (uIoc_subset_uIcc hs))
            (norm_nonneg _)))
        ((hy.norm.mono_set hsub).const_mul ε)
    calc
      _ ≤ |∫ s in v..x, ε * ‖y s‖| := hi
      _ = ε * ‖N x - N v‖ := by
        rw [intervalIntegral.integral_const_mul, abs_mul, abs_of_pos hε, Real.norm_eq_abs]
        congr 2
        exact (intervalIntegral.integral_interval_sub_left
          (hy.norm.mono_set hxc) (hy.norm.mono_set hvc)).symm
  have hdz : HasDerivAt z 0 v := by
    apply HasDerivAt.of_isLittleO
    simpa only [smul_zero, sub_zero] using hsmall.trans_isBigO hdn.isBigO_sub
  have hd := hdz.add (hdy.const_mul (P v))
  simpa only [Pi.add_def, z, A, Y, sub_add_cancel, zero_add] using hd

/-- [internal] There is one full-measure set of labels on which FTC holds
simultaneously for every continuous multiplier. In particular it works for an
uncountable family of incoming parameters. Only the initial density is L¹. -/
theorem ae_forall_continuous_weight_hasDerivAt {y : ℝ → ℂ} {c d : ℝ} (hcd : c ≤ d)
    (hy : IntervalIntegrable y volume c d) :
    ∀ᵐ v ∂volume.restrict (Icc c d), ∀ P : ℝ → ℂ,
      ContinuousOn P (Icc c d) →
      HasDerivAt (fun x => ∫ s in c..x, P s * y s) (P v * y v) v := by
  apply (ae_restrict_iff' measurableSet_Icc).mpr
  have hne (x : ℝ) : ∀ᵐ y : ℝ, y ≠ x := by simp [ae_iff]
  filter_upwards [hy.ae_hasDerivAt_integral, hy.norm.ae_hasDerivAt_integral,
    hne c, hne d] with v hv hn hvc hvd hvm P hP
  have hvi : v ∈ Ioo c d := ⟨lt_of_le_of_ne hvm.1 (Ne.symm hvc),
    lt_of_le_of_ne hvm.2 hvd⟩
  exact hasDerivAt_weighted_primitive hy (by rwa [uIcc_of_le hcd]) hvi
    (hv (by rwa [uIcc_of_le hcd]) c left_mem_uIcc)
    (hn (by rwa [uIcc_of_le hcd]) c left_mem_uIcc)

end EmcsfAcExtension.Global.Density
