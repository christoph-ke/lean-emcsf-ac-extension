module

public import EmcsfAcExtension.Global.Calculus.WeakDensity
public import EmcsfAcExtension.Infra.Density.Representative
public import EmcsfAcExtension.Global.Defs.Original
import EmcsfAcExtension.Local.Calculus.Sections

/-! # Identification of the transported outgoing density

Fubini first identifies a primitive on every incoming row. The incoming
linear ODE identifies that primitive's density with variation of constants.
The common-label FTC then supplies the Lebesgue-point step required for one
exceptional label set before the quantifier over all incoming times.
-/

public section

open Set MeasureTheory Filter Topology Complex

namespace EmcsfAcExtension.Global.Calculus

/-- [internal] The linear density multiplier is the expansion ratio times
the unitary gauge phase. The only transport premise is the characteristic
expansion equation; the field-level consumer supplies it from `IsSolution`.
There is no choice of a terminal constant or expansion lower bound. -/
theorem exp_integral_eq_ratio_phase_of_transport (e : ℝ)
    {l A : ℝ → ℝ} {C : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hl : AbsolutelyContinuousOnInterval l a b) (hne : ∀ u ∈ Icc a b, l u ≠ 0)
    (hC : IntervalIntegrable C volume a b) (hA : IntervalIntegrable A volume a b)
    (heq : ∀ᵐ u ∂volume.restrict (Icc a b), HasDerivAt (fun x => (l x : ℂ))
      (-(C u + I * e * A u) * l u) u) :
    ∀ u ∈ Icc a b, Complex.exp (∫ s in a..u, C s) =
      (l a / l u : ℝ) * Complex.exp (-I * e * ∫ s in a..u, A s) := by
  let E : ℝ → ℂ := fun u => Complex.exp (∫ s in a..u, C s)
  let P : ℝ → ℂ := fun u => Complex.exp (I * e * ∫ s in a..u, A s)
  let Z : ℝ → ℂ := fun u => (l u : ℂ) * E u * P u
  have hE := hC.absolutelyContinuousOnInterval_intervalIntegral_complex left_mem_uIcc
  have hP := (hA.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc).const_mul e
  have hPac : AbsolutelyContinuousOnInterval P a b := by
    apply hP.unit_phase.congr
    intro u hu
    simp only [P, Complex.ofReal_mul]
    congr 1
    ring
  have hZ := (hl.ofReal.mul_normed_ring hE.cexp).mul_normed_ring hPac
  have hd : ∀ᵐ u, u ∈ uIcc a b → HasDerivAt Z 0 u := by
    filter_upwards [(ae_restrict_iff' measurableSet_Icc).1 heq,
      hC.ae_hasDerivAt_integral, hA.ae_hasDerivAt_integral] with u hlu hCu hAu hu
    have hdE := (hCu hu a left_mem_uIcc).cexp
    have hdP := ((hAu hu a left_mem_uIcc).ofReal_comp.const_mul (I * e)).cexp
    have hdu := ((hlu (by simpa [uIcc_of_le hab] using hu)).mul hdE).mul hdP
    convert hdu using 1
    simp only [Pi.mul_apply]
    ring
  obtain ⟨z, hz⟩ := hZ.const_of_ae_hasDerivAt_zero hd
  have ha : (l a : ℂ) = z := by
    simpa only [P, intervalIntegral.integral_same, Complex.ofReal_zero, mul_zero,
      Complex.exp_zero, mul_one] using! hz a left_mem_uIcc
  intro u hu
  have hu' := hz u (by simpa [uIcc_of_le hab] using hu)
  rw [← ha] at hu'
  have he : P u * Complex.exp (-I * e * ∫ s in a..u, A s) = 1 := by
    change Complex.exp (I * e * ∫ s in a..u, A s) *
      Complex.exp (-I * e * ∫ s in a..u, A s) = 1
    rw [← Complex.exp_add]
    have hzero : (I * e * ∫ s in a..u, A s) + (-I * e * ∫ s in a..u, A s) = (0 : ℂ) := by
      ring
    rw [hzero, Complex.exp_zero]
  have hY : E u * P u = (l a : ℂ) / l u := (eq_div_iff (Complex.ofReal_ne_zero.mpr
    (hne u hu))).2 (by simpa only [Z, E, mul_assoc, mul_comm, mul_left_comm] using! hu')
  calc
    E u = E u * (P u * Complex.exp (-I * e * ∫ s in a..u, A s)) := by rw [he, mul_one]
    _ = ((l a / l u : ℝ) : ℂ) * Complex.exp (-I * e * ∫ s in a..u, A s) := by
      rw [← mul_assoc, hY, Complex.ofReal_div]

/-- [internal] Characteristic integral equations identify a fixed transported
density on one common full-measure set of labels. The outgoing equation for
`G` is an explicit helper premise, discharged from the normalized equations
by its field-level consumer. The final common-label FTC uses the fixed L¹
initial density, with no continuous outgoing derivative hypothesis. -/
theorem fixed_density_of_characteristic_forms
    {f G C F w : ℝ → ℝ → ℂ} {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hC : Continuous C.uncurry) (hF : Continuous F.uncurry)
    (hw : StronglyMeasurable w.uncurry)
    (hH : Integrable (fun p : ℝ × ℝ => C p.1 p.2 * w p.1 p.2 + F p.1 p.2)
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))))
    (hf₀ : AbsolutelyContinuousOnInterval (f a) c d)
    (hfw : ∀ u ∈ Icc a b, ∀ᵐ v ∂volume.restrict (Icc c d),
      HasDerivAt (f u) (w u v) v)
    (hin : ∀ v ∈ Icc c d, ∀ u ∈ Icc a b,
      IntegralForm (fun s => f s v) (fun s => G s v) a u)
    (hout : ∀ u ∈ Icc a b, ∀ v ∈ Icc c d,
      IntegralForm (G u) (fun t => C u t * w u t + F u t) c v) :
    ∀ᵐ v ∂volume.restrict (Icc c d), ∀ u ∈ Icc a b,
      HasDerivAt (f u) (Density.transportDensity C F (deriv (f a)) a u v) v := by
  let H : ℝ → ℝ → ℂ := fun u v => C u v * w u v + F u v
  let Z : ℝ → ℝ → ℂ := fun u v => deriv (f a) v + ∫ s in a..u, H s v
  have hprim := primitive_identity_of_characteristic_forms (H := H) hab.le hcd.le hf₀ hH hin hout
  have hHi (u : ℝ) (hu : u ∈ Icc a b) :
      IntervalIntegrable (fun v => ∫ s in a..u, H s v) volume c d := by
    have hh : Integrable H.uncurry
        ((volume.restrict (uIoc a u)).prod (volume.restrict (Icc c d))) :=
      hH.mono_measure (Measure.prod_mono (Measure.restrict_mono (by
        rw [uIoc_of_le hu.1]
        exact Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl hu.2)) le_rfl) le_rfl)
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hcd.le).2
    simpa only [Function.uncurry, intervalIntegral.integral_of_le hu.1,
      uIoc_of_le hu.1] using! hh.integral_prod_right
  have hZi (u : ℝ) (hu : u ∈ Icc a b) : IntervalIntegrable (Z u) volume c d :=
    hf₀.intervalIntegrable_deriv_complex.add (hHi u hu)
  have hrow (u : ℝ) (hu : u ∈ Icc a b) :
      ∀ᵐ v ∂volume.restrict (Icc c d), HasDerivAt (f u) (Z u v) v := by
    apply (ac_ae_of_integralForm_on hcd.le (fun v hv => ?_)).2
    refine ⟨(hZi u hu).mono_set (by
      rw [uIcc_of_le hv.1, uIcc_of_le hcd.le]
      exact Icc_subset_Icc le_rfl hv.2), ?_⟩
    rw [hprim u hu v hv]
    abel
  have hroweq : ∀ u ∈ Icc a b, w u =ᵐ[volume.restrict (Icc c d)] Z u := by
    intro u hu
    filter_upwards [hfw u hu, hrow u hu] with v hv hz
    exact hv.unique hz
  have hZsm : StronglyMeasurable Z.uncurry :=
    ((measurable_deriv (f a)).stronglyMeasurable.comp_measurable measurable_snd).add
      (Density.stronglyMeasurable_incoming_primitive
        (hC.stronglyMeasurable.mul hw |>.add hF.stronglyMeasurable) a)
  have hswap : ∀ᵐ v ∂volume.restrict (Icc c d),
      (fun u => w u v) =ᵐ[volume.restrict (Icc a b)] (fun u => Z u v) := by
    apply (Measure.ae_ae_comm (hw.measurableSet_eq_fun hZsm)).1
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    exact hroweq u hu
  have hZac := Density.ae_absolutelyContinuousOnInterval_incoming_primitive (H := H)
    (deriv (f a)) hab.le hH
  have hZd := Density.ae_ae_hasDerivAt_incoming_primitive (H := H) (deriv (f a)) hab.le hH
  have hZto : ∀ᵐ v ∂volume.restrict (Icc c d), ∀ u ∈ Icc a b,
      Z u v = Density.transportDensity C F (deriv (f a)) a u v := by
    filter_upwards [hswap, hZac, hZd] with v hwz hzac hzd
    apply Density.eq_transportDensity_of_ac_deriv_eq hab.le hzac
      ((hC.comp (continuous_id.prodMk continuous_const)).intervalIntegrable a b)
      ((hF.comp (continuous_id.prodMk continuous_const)).intervalIntegrable a b)
      ?_ (by simp)
    filter_upwards [hwz, hzd] with u hwu hdu
    rw [hdu.deriv]
    change C u v * w u v + F u v = C u v * Z u v + F u v
    rw [hwu]
  obtain ⟨P, R, hP, hR, hPR⟩ := Density.exists_continuousOn_transport_factors hab.le hcd.le
    hC.continuousOn hF.continuousOn
  have hrep : ∀ u ∈ Icc a b, ∀ v ∈ Icc c d,
      f u v = f u c + ∫ t in c..v, Density.fixedDensity P R (deriv (f a)) u t := by
    intro u hu v hv
    rw [hprim u hu v hv]
    congr 1
    apply intervalIntegral.integral_congr_ae
    apply (ae_restrict_iff' measurableSet_uIoc).1
    have hsub : uIoc c v ⊆ Icc c d := by
      rw [uIoc_of_le hv.1]
      exact Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl hv.2)
    filter_upwards [ae_restrict_of_ae
      ((ae_restrict_iff' measurableSet_Icc).1 hZto),
      ae_restrict_mem measurableSet_uIoc] with t ht htm
    exact (ht (hsub htm) u hu).trans (hPR _ u hu t (hsub htm))
  filter_upwards [Density.ae_forall_hasDerivAt_of_fixedDensity_representation hcd.le
    hP hR hf₀.intervalIntegrable_deriv_complex hrep,
    ae_restrict_mem measurableSet_Icc] with v hv hvm u hu
  have hd := hv u hu
  rw [← hPR _ u hu v hvm] at hd
  exact hd

/-- [internal] On a proper solution rectangle the abstract integrating
factor is exactly the adopted expansion-ratio/phase formula. The coefficient
and forcing equalities describe continuous extensions used only for the
abstract calculus; their consumer constructs them by clamping. -/
theorem densityRepresentative_eq_transportDensity_of_coefficients
    {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)} (hS : IsSolution e S D)
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hrect : Icc a b ×ˢ Icc c d ⊆ D ∩ {p | p.1 < p.2})
    {C F : ℝ → ℝ → ℂ} (hC : Continuous C.uncurry)
    (hCe : ∀ p ∈ Icc a b ×ˢ Icc c d,
      C p.1 p.2 =
        ((-S.nu p.1 p.2 / ((1 - S.mu p.1 p.2) * S.r p.1 p.2) *
          (S.mu p.1 p.2 - S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2) : ℝ) : ℂ) -
        I * e * S.A p.1 p.2)
    (hFe : EqOn F.uncurry (rawDensitySource e S).uncurry (Icc a b ×ˢ Icc c d)) :
    ∀ u ∈ Icc a b, ∀ v ∈ Icc c d,
      densityRepresentative e S a u v =
        Density.transportDensity C F (deriv (S.a a)) a u v := by
  have hbc : b < c := (hrect (show (b, c) ∈ Icc a b ×ˢ Icc c d from
    ⟨⟨hab.le, le_rfl⟩, ⟨le_rfl, hcd.le⟩⟩)).2
  have hseg {s t v : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hv : v ∈ Icc c d) :
      inSeg s t v ⊆ D := by
    rintro ⟨x, y⟩ ⟨hsx, hxt, rfl⟩
    exact (hrect ⟨⟨hs.1.trans hsx, hxt.trans ht.2⟩, hv⟩).1
  have hE (s t v : ℝ) (hst : s ≤ t) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
      (hv : v ∈ Icc c d) :
      Complex.exp (∫ x in s..t, C x v) =
        (S.lam s v / S.lam t v : ℝ) * Complex.exp (-I * e * ∫ x in s..t, S.A x v) := by
    have hsec := Local.IsSolution.in_section hS hst (ht.2.trans_lt (hbc.trans_le hv.1))
      (hseg hs ht hv)
    apply exp_integral_eq_ratio_phase_of_transport e hst hsec.2.1.1
      (fun x hx => (hS.lam_pos (x, v) ((hrect
        ⟨⟨hs.1.trans hx.1, hx.2.trans ht.2⟩, hv⟩).1)).ne')
      ((hC.comp (continuous_id.prodMk continuous_const)).intervalIntegrable s t)
      ((continuousOn_in_section hS.cont_A (hseg hs ht hv)).intervalIntegrable_of_Icc hst)
    · filter_upwards [hsec.2.1.2, ae_restrict_mem measurableSet_Icc] with x hx hxm
      apply hx.ofReal_comp.congr_deriv
      change (S.rUV x v : ℂ) = -(C x v + I * e * S.A x v) * S.lam x v
      rw [hCe (x, v) ⟨⟨hs.1.trans hxm.1, hxm.2.trans ht.2⟩, hv⟩]
      have halg := congrArg (fun z : ℝ => (z : ℂ)) (density_coefficient_mul_lam S x v)
      push_cast at halg ⊢
      linear_combination halg
    · exact ⟨hst, le_rfl⟩
  intro u hu v hv
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  have hcint (x : ℝ) : IntervalIntegrable (fun y => C y v) volume a x :=
    (hC.comp (continuous_id.prodMk continuous_const)).intervalIntegrable a x
  symm
  rw [Density.transportDensity, mul_add, ← intervalIntegral.integral_const_mul]
  unfold densityRepresentative
  congr 1
  · rw [hE a u v hu.1 ha hu hv]
  · apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hu.1] at hs
    have hs' : s ∈ Icc a b := ⟨hs.1, hs.2.trans hu.2⟩
    have he : Complex.exp (∫ x in a..u, C x v) * Complex.exp (-(∫ x in a..s, C x v)) =
        Complex.exp (∫ x in s..u, C x v) := by
      rw [← Complex.exp_add, ← sub_eq_add_neg,
        intervalIntegral.integral_interval_sub_left (hcint u) (hcint s)]
    change Complex.exp (∫ x in a..u, C x v) *
      (Complex.exp (-(∫ x in a..s, C x v)) * F s v) =
        (S.lam s v / S.lam u v : ℝ) * Complex.exp (-I * e * ∫ x in s..u, S.A x v) *
          rawDensitySource e S s v
    have hFs : F s v = rawDensitySource e S s v := hFe (show (s, v) ∈
      Icc a b ×ˢ Icc c d from ⟨hs', hv⟩)
    rw [← mul_assoc, he, hE s u v hs.2 hs' hu hv, hFs]

/-- [internal] The canonical density has continuous rectangular factors and
the prescribed normalized field as its primitive on every row. The initial
factor is exactly `deriv (S.a a)`, with only the L¹ regularity supplied by AC.
No conclusion-shaped hypothesis is added to the frozen class. -/
theorem exists_density_factors {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hrect : Icc a b ×ˢ Icc c d ⊆ D ∩ {p | p.1 < p.2}) :
    ∃ P R : ℝ → ℝ → ℂ,
      ContinuousOn P.uncurry (Icc a b ×ˢ Icc c d) ∧
      ContinuousOn R.uncurry (Icc a b ×ˢ Icc c d) ∧
      (∀ u ∈ Icc a b, ∀ v ∈ Icc c d,
        densityRepresentative e S a u v = Density.fixedDensity P R (deriv (S.a a)) u v) ∧
      (∀ u ∈ Icc a b, ∀ v ∈ Icc c d,
        S.a u v = S.a u c + ∫ t in c..v, Density.fixedDensity P R (deriv (S.a a)) u t) := by
  let C₀ : ℝ → ℝ → ℂ := fun u v =>
    ((-S.nu u v / ((1 - S.mu u v) * S.r u v) *
      (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) : ℝ) : ℂ) - I * e * S.A u v
  let G : ℝ → ℝ → ℂ := fun u v =>
    (-S.nu u v / ((1 - S.mu u v) * S.r u v) : ℝ) *
      (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2 : ℝ) * (S.a u v - S.phi u v) +
      I * e * (-S.nu u v / ((1 - S.mu u v) * S.r u v) : ℝ) * S.Q u v * S.phi u v -
      I * e * S.A u v * S.a u v
  have hD : Icc a b ×ˢ Icc c d ⊆ D := fun p hp => (hrect hp).1
  have hbc : b < c := (hrect (show (b, c) ∈ Icc a b ×ˢ Icc c d from
    ⟨⟨hab.le, le_rfl⟩, ⟨le_rfl, hcd.le⟩⟩)).2
  have houtseg (u : ℝ) (hu : u ∈ Icc a b) : outSeg u c d ⊆ D := by
    rintro ⟨x, y⟩ ⟨rfl, hy⟩
    exact hD ⟨hu, hy⟩
  obtain ⟨C, hC, hCe⟩ := exists_continuous_rectangle_extension (f := C₀) hab.le hcd.le
    (continuousOn_density_coefficient hS hrect)
  obtain ⟨F, hF, hFe⟩ := exists_continuous_rectangle_extension hab.le hcd.le
    (continuousOn_rawDensitySource hS hrect)
  obtain ⟨f, hf, hfe⟩ := exists_continuous_rectangle_extension hab.le hcd.le
    ((continuousOn_a hS).mono hD)
  let w : ℝ → ℝ → ℂ := fun u v => deriv (f u) v
  have hw : StronglyMeasurable w.uncurry := stronglyMeasurable_deriv_with_param hf
  have hgood : ∀ᵐ p ∂(volume.restrict (Icc a b)).prod (volume.restrict (Icc c d)),
      p ∈ Icc a b ×ˢ Ioo c d := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Icc.prod measurableSet_Ioo)).2
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact (ae_restrict_mem measurableSet_Ioo).mono fun v hv => ⟨hu, hv⟩
  have hwi : Integrable w.uncurry
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) := by
    apply (integrable_normalized_outgoing_deriv hS hab.le hcd hD).congr
    filter_upwards [hgood] with p hp
    exact (outgoing_deriv_eq_of_eqOn_rectangle hfe hp.1 hp.2).symm
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (hC.continuousOn (s := Icc a b ×ˢ Icc c d))
  have hFi : Integrable F.uncurry
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) := by
    simpa only [Measure.prod_restrict, ← Measure.volume_eq_prod] using!
      hF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hHi := (hwi.bdd_mul hC.aestronglyMeasurable
    (hgood.mono fun p hp => hB p ⟨hp.1, Ioo_subset_Icc_self hp.2⟩)).add hFi
  have hfw : ∀ u ∈ Icc a b, ∀ᵐ v ∂volume.restrict (Icc c d),
      HasDerivAt (S.a u) (w u v) v := by
    intro u hu
    have hac := (hS.ac_out u c d hcd.le (houtseg u hu)).2.2.2.2
    rw [← restrict_Ioo_eq_restrict_Icc]
    filter_upwards [ae_restrict_of_ae hac.ae_differentiableAt_of_mem_uIcc,
      ae_restrict_mem measurableSet_Ioo] with v hd hv
    exact (hd (by rw [uIcc_of_le hcd.le]; exact Ioo_subset_Icc_self hv)).hasDerivAt.congr_deriv
      (outgoing_deriv_eq_of_eqOn_rectangle hfe hu hv).symm
  have hin : ∀ v ∈ Icc c d, ∀ u ∈ Icc a b,
      IntegralForm (fun s => S.a s v) (fun s => G s v) a u := by
    intro v hv u hu
    have hi := constant_label_connector_calculus hS hu.1
      (hu.2.trans_lt (hbc.trans_le hv.1)) (by
        rintro ⟨x, y⟩ ⟨hx, hxu, rfl⟩
        exact hD ⟨⟨hx, hxu.trans hu.2⟩, hv⟩)
    simpa only [normalized_incoming_source_eq, G] using! hi
  have hout : ∀ u ∈ Icc a b, ∀ v ∈ Icc c d,
      IntegralForm (G u) (fun t => C u t * w u t + F u t) c v := by
    intro u hu v hv
    have hsrc := normalized_source_out_section hS (hu.2.trans_lt hbc) hcd.le (houtseg u hu)
    have hsub : uIcc c v ⊆ uIcc c d := by
      rw [uIcc_of_le hv.1, uIcc_of_le hcd.le]
      exact Icc_subset_Icc le_rfl hv.2
    apply integralForm_of_ac_of_ae_deriv_eq (hsrc.1.mono hsub)
    apply (ae_restrict_iff' measurableSet_uIcc).2
    filter_upwards [(ae_restrict_iff' measurableSet_Icc).1 hsrc.2,
      (ae_restrict_iff' measurableSet_Icc).1 (hfw u hu)] with t ht hwf htm
    have ht' : t ∈ Icc c d := by simpa only [uIcc_of_le hcd.le] using hsub htm
    have hp : (u, t) ∈ Icc a b ×ˢ Icc c d := ⟨hu, ht'⟩
    have hCt : C u t = C₀ u t := hCe hp
    have hFt : F u t = rawDensitySource e S u t := hFe hp
    rw [(ht ht').deriv, (hwf ht').deriv, hCt, hFt]
    simp only [C₀, Complex.ofReal_mul]
  have h₀ := (hS.ac_out a c d hcd.le (houtseg a ⟨le_rfl, hab.le⟩)).2.2.2.2
  have hcommon := fixed_density_of_characteristic_forms hab hcd hC hF hw hHi h₀ hfw hin hout
  have hcanonical := densityRepresentative_eq_transportDensity_of_coefficients hS hab hcd
    hrect hC (fun p hp => hCe hp) hFe
  obtain ⟨P, R, hP, hR, hPR⟩ := Density.exists_continuousOn_transport_factors hab.le hcd.le
    hC.continuousOn hF.continuousOn
  refine ⟨P, R, hP, hR, fun u hu v hv => (hcanonical u hu v hv).trans (hPR _ u hu v hv), ?_⟩
  intro u hu v hv
  have hac := (hS.ac_out u c d hcd.le (houtseg u hu)).2.2.2.2
  have hI := Density.intervalIntegrable_fixedDensity hcd.le hu hP hR
    h₀.intervalIntegrable_deriv_complex
  have hsub : uIcc c v ⊆ uIcc c d := by
    rw [uIcc_of_le hv.1, uIcc_of_le hcd.le]
    exact Icc_subset_Icc le_rfl hv.2
  have hd : ∀ᵐ t, t ∈ uIcc c d →
      HasDerivAt (S.a u) (Density.fixedDensity P R (deriv (S.a a)) u t) t := by
    filter_upwards [(ae_restrict_iff' measurableSet_Icc).1 hcommon] with t ht htm
    have ht' : t ∈ Icc c d := by simpa only [uIcc_of_le hcd.le] using htm
    rw [← hPR _ u hu t ht']
    exact ht ht' u hu
  rw [(hac.mono hsub).integral_eq_sub_of_ae_hasDerivAt_complex (hI.mono_set hsub)
    (hd.mono fun t ht htm => ht (hsub htm))]
  abel

/-- [node sec:charged-equations#fixed-initial-density-representation]
The one-null-set fixed-density representation on every proper rectangle of
the original AC development. The common-label FTC includes the required
Lebesgue-point step; the initial derivative is only L¹. -/
theorem fixed_density_representation (ui e : ℝ) (S : Fields)
    (h : OriginalData ui e S) (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    (hrect : Icc a b ×ˢ Icc c d ⊆ origDomain ui ∩ {p | p.1 < p.2}) :
    ∀ᵐ v ∂volume.restrict (Icc c d), ∀ u ∈ Icc a b,
      HasDerivAt (S.a u) (densityRepresentative e S a u v) v := by
  obtain ⟨P, R, hP, hR, heq, hprim⟩ := exists_density_factors h.solution hab hcd hrect
  have hinit := (h.solution.ac_out a c d hcd.le (by
    rintro ⟨x, y⟩ ⟨rfl, hy⟩
    exact (hrect ⟨⟨le_rfl, hab.le⟩, hy⟩).1)).2.2.2.2
  filter_upwards [Density.ae_forall_hasDerivAt_of_fixedDensity_representation hcd.le
    hP hR hinit.intervalIntegrable_deriv_complex hprim,
    ae_restrict_mem measurableSet_Icc] with v hv hvm u hu
  rw [heq u hu v hvm]
  exact hv u hu

/-- [node sec:charged-equations#weak-outgoing-density-transport]
The prescribed outgoing density is AC on every incoming section, with its
linear incoming equation a.e. and the displayed continuous source. This is
the sectional weak meaning of the differentiated equation; the fixed-density
theorem identifies this representative with the field's outgoing derivative.
The conclusion holds for every label, with no restriction to a curve. -/
theorem weak_outgoing_density_transport
    {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)} (hS : IsSolution e S D)
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hrect : Icc a b ×ˢ Icc c d ⊆ D ∩ {p | p.1 < p.2}) :
    ∀ v ∈ Icc c d,
      AbsolutelyContinuousOnInterval (fun u => densityRepresentative e S a u v) a b ∧
      ∀ᵐ u ∂volume.restrict (Icc a b),
        HasDerivAt (fun x => densityRepresentative e S a x v)
          (((-S.nu u v / ((1 - S.mu u v) * S.r u v) *
              (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) : ℝ) - I * e * S.A u v) *
            densityRepresentative e S a u v + rawDensitySource e S u v) u := by
  let C₀ : ℝ → ℝ → ℂ := fun u v =>
    ((-S.nu u v / ((1 - S.mu u v) * S.r u v) *
      (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) : ℝ) : ℂ) - I * e * S.A u v
  obtain ⟨C, hC, hCe⟩ := exists_continuous_rectangle_extension (f := C₀) hab.le hcd.le
    (continuousOn_density_coefficient hS hrect)
  have hEq := densityRepresentative_eq_transportDensity_of_coefficients
    (F := rawDensitySource e S) hS hab hcd hrect hC (fun p hp => hCe hp) (fun _ _ => rfl)
  have hT := Density.forall_transportDensity_ac_and_ae_deriv (deriv (S.a a)) hab.le
    hC.continuousOn (continuousOn_rawDensitySource hS hrect)
  intro v hv
  refine ⟨(hT v hv).1.congr (fun u hu =>
    (hEq u (by simpa [uIcc_of_le hab.le] using hu) v hv).symm), ?_⟩
  rw [← restrict_Ioo_eq_restrict_Icc]
  filter_upwards [((hT v hv).2).filter_mono
    (ae_mono (Measure.restrict_mono Ioo_subset_Icc_self le_rfl)),
    ae_restrict_mem measurableSet_Ioo] with u hu hum
  have hd := hu.congr_of_eventuallyEq (by
    filter_upwards [Ioo_mem_nhds hum.1 hum.2] with x hx
    exact hEq x (Ioo_subset_Icc_self hx) v hv)
  rw [← hEq u (Ioo_subset_Icc_self hum) v hv] at hd
  have hc : C u v = C₀ u v := hCe (show (u, v) ∈ Icc a b ×ˢ Icc c d from
    ⟨Ioo_subset_Icc_self hum, hv⟩)
  simpa only [hc, C₀] using! hd

end EmcsfAcExtension.Global.Calculus
