module

public import EmcsfAcExtension.Global.Exterior.VariationTransport
public import EmcsfAcExtension.Global.Exterior.VariationTailsModulus

/-! # The modulus history on the actual swept exterior

This file supplies M2 and the proper-set finiteness needed for M3 of
approved internal project record, `charged_SF_new_version.tex:L1337–L1340`, L1413–L1416.
The field density is always the prescribed representative anchored at
the initial row. All estimate coefficients are exactly one.
-/

public section

open Set MeasureTheory Filter Topology Complex

namespace EmcsfAcExtension.Global.Exterior

/-- [internal] The nonnegative history density in the incoming modulus
inequality, including the real coefficient and all charged source terms. -/
@[expose] noncomputable def densityModulusHistory (e : ℝ) (S : Fields) (a : ℝ)
    (p : ℝ × ℝ) : ℝ :=
  |(densityTransportCoefficient e S p.1 p.2).re| *
    ‖densityRepresentative e S a p.1 p.2‖ + ‖rawDensitySource e S p.1 p.2‖

/-- [internal] The history integrand is nonnegative at every point,
including exceptional initial labels. -/
theorem densityModulusHistory_nonneg (e : ℝ) (S : Fields) (a : ℝ) (p : ℝ × ℝ) :
    0 ≤ densityModulusHistory e S a p :=
  add_nonneg (mul_nonneg (abs_nonneg _) (norm_nonneg _)) (norm_nonneg _)

/-- [internal]
The actual prescribed density satisfies the integrated modulus inequality
to every proper incoming endpoint, at every label. The imaginary connection
is removed before taking norms. Its coefficient is exactly one, uniform in
the solution, coupling, label and endpoints. -/
theorem density_norm_le_initial_add_history
    {ui e a b v : ℝ} {S : Fields} (hS : IsSolution e S (origDomain ui))
    (hia : ui ≤ a) (hab : a ≤ b) (hbv : b < v) (hv0 : v ≤ 0) :
    ‖densityRepresentative e S a b v‖ ≤ ‖deriv (S.a a) v‖ +
      ∫ u in a..b, densityModulusHistory e S a (u, v) := by
  have hs : inSeg a b v ⊆ origDomain ui ∩ {p | p.1 < p.2} := by
    rintro ⟨u, w⟩ ⟨hu₁, hu₂, rfl⟩
    exact ⟨⟨hia.trans hu₁, hu₂.trans_lt (hbv.trans_le hv0),
      (hu₂.trans_lt hbv).le, hv0⟩, hu₂.trans_lt hbv⟩
  have hC : ContinuousOn (fun u => densityTransportCoefficient e S u v) (Icc a b) :=
    (Calculus.continuousOn_density_coefficient hS hs).comp (f := fun u : ℝ => (u, v))
      (continuous_id.prodMk continuous_const).continuousOn (fun u hu => ⟨hu.1, hu.2, rfl⟩)
  have hF : ContinuousOn (fun u => rawDensitySource e S u v) (Icc a b) :=
    (Calculus.continuousOn_rawDensitySource hS hs).comp (f := fun u : ℝ => (u, v))
      (continuous_id.prodMk continuous_const).continuousOn (fun u hu => ⟨hu.1, hu.2, rfl⟩)
  have ht := density_transport_on_incoming_history hS hia hab hbv hv0
  have hid (z : ℂ) : (z.re : ℂ) - I * (-z.im : ℝ) = z := by
    calc
      _ = (z.re : ℂ) + (z.im : ℂ) * I := by simp only [ofReal_neg]; ring
      _ = z := Complex.re_add_im z
  have hd : ∀ᵐ u ∂volume.restrict (Icc a b),
      deriv (fun x => densityRepresentative e S a x v) u =
        (((densityTransportCoefficient e S u v).re : ℂ) -
          I * (-(densityTransportCoefficient e S u v).im : ℝ)) *
            densityRepresentative e S a u v + rawDensitySource e S u v := by
    filter_upwards [ht.2] with u hu
    rw [hu.deriv, hid]
  have hn := norm_le_initial_add_integral_of_covariant_transport hab ht.1
    (Complex.continuous_re.comp_continuousOn hC)
    (Complex.continuous_im.comp_continuousOn hC).neg (hF.intervalIntegrable_of_Icc hab) hd
  rw [densityRepresentative_initial_of_mem hS
    (hs ⟨le_rfl, hab, rfl⟩).1] at hn
  exact hn

/-- [internal]
The actual prescribed density is integrable on the full proper swept
domain. The sole rough factor is its fixed L¹ initial derivative. The
majorant constant is local to this solution, coupling, boundary and proper
interval; it is fixed before the two coordinates vary. -/
theorem integrableOn_swept_density
    {ui e a b : ℝ} {S : Fields} {t : ℝ → ℝ}
    (hS : IsSolution e S (origDomain ui)) (hab : a ≤ b)
    (ht : ContinuousOn t (Icc a b)) (hm : MonotoneOn t (Icc a b))
    (hmem : ∀ u ∈ Icc a b, (u, t u) ∈ origDomain ui)
    (hproper : ∀ u ∈ Icc a b, u < t u) :
    IntegrableOn (fun p => densityRepresentative e S a p.1 p.2)
      (variationSweptDomain a b t) (volume.prod volume) := by
  let K := variationSweptDomain a b t
  have hK : MeasurableSet K := (isClosed_variationSweptDomain hab ht).measurableSet
  obtain ⟨C, hC, hI, hb⟩ := exists_swept_density_bound hS hab ht hm hmem hproper
  have hta : t a ≤ 0 := (hmem a ⟨le_rfl, hab⟩).2.2.2
  have hmaj : IntegrableOn (fun p : ℝ × ℝ => C * (‖deriv (S.a a) p.2‖ + 1))
      (Icc a b ×ˢ Icc (t a) 0) (volume.prod volume) := by
    rw [IntegrableOn, ← Measure.prod_restrict]
    exact ((intervalIntegrable_iff_integrableOn_Icc_of_le hta).1 hI).comp_snd _
  have hsub : K ⊆ Icc a b ×ˢ Icc (t a) 0 := by
    rintro ⟨u, v⟩ ⟨hu, hv⟩
    exact ⟨hu, (hm ⟨le_rfl, hab⟩ hu hu.1).trans hv.1, hv.2⟩
  have hmeas := (measurable_stopped_swept_density hS hab ht hm hmem hproper).aestronglyMeasurable
    (μ := (volume.prod volume).restrict K)
  have hmeas' : AEStronglyMeasurable (fun p => densityRepresentative e S a p.1 p.2)
      ((volume.prod volume).restrict K) := by
    apply hmeas.congr
    filter_upwards [ae_restrict_mem hK] with p hp
    exact indicator_of_mem hp _
  apply Integrable.mono' (hmaj.mono_set hsub) hmeas'
  filter_upwards [ae_restrict_mem hK] with p hp
  exact hb p hp

/-- [internal]
The complete modulus history is L¹ on the exact proper swept domain.
This establishes the finiteness needed after the stopped-history Fubini
identity; there is no assumption on a bounding rectangle through the axis. -/
theorem integrableOn_densityModulusHistory
    {ui e a b : ℝ} {S : Fields} {t : ℝ → ℝ}
    (hS : IsSolution e S (origDomain ui)) (hab : a ≤ b)
    (ht : ContinuousOn t (Icc a b)) (hm : MonotoneOn t (Icc a b))
    (hmem : ∀ u ∈ Icc a b, (u, t u) ∈ origDomain ui)
    (hproper : ∀ u ∈ Icc a b, u < t u) :
    IntegrableOn (densityModulusHistory e S a) (variationSweptDomain a b t)
      (volume.prod volume) := by
  have hK := isCompact_variationSweptDomain hab ht hm
  have hs := variationSweptDomain_subset hmem hproper
  have hC : ContinuousOn (fun p => |(densityTransportCoefficient e S p.1 p.2).re|)
      (variationSweptDomain a b t) :=
    (Complex.continuous_re.comp_continuousOn
      (Calculus.continuousOn_density_coefficient hS hs)).abs
  have hF := (Calculus.continuousOn_rawDensitySource hS hs).norm
  exact (IntegrableOn.continuousOn_mul hC
    (integrableOn_swept_density hS hab ht hm hmem hproper).norm hK).add
      (hF.integrableOn_compact hK)

/-- [internal] The history is integrable on every proper outgoing row,
with any earlier fixed anchor. This is sectional L¹ control, not a
restriction of a product-almost-everywhere derivative. -/
theorem densityModulusHistory_intervalIntegrable_on_row
    {ui e a u v : ℝ} {S : Fields} (hS : IsSolution e S (origDomain ui))
    (hia : ui ≤ a) (hau : a ≤ u) (huv : u < v) (hv0 : v ≤ 0) :
    IntervalIntegrable (fun w => densityModulusHistory e S a (u, w)) volume v 0 := by
  have hmem (x : ℝ) (hx : x ∈ Icc a u) : (x, v) ∈ origDomain ui :=
    ⟨hia.trans hx.1, hx.2.trans_lt (huv.trans_le hv0), (hx.2.trans_lt huv).le, hv0⟩
  have hp (x : ℝ) (hx : x ∈ Icc a u) : x < v := hx.2.trans_lt huv
  have hw := (swept_density_row_primitive hS hau hmem hp ⟨hau, le_rfl⟩).1
  have hout : outSeg u v 0 ⊆ origDomain ui ∩ {p | p.1 < p.2} := by
    rintro ⟨x, w⟩ ⟨rfl, hvw⟩
    exact ⟨⟨hia.trans hau, huv.trans_le hv0, huv.le.trans hvw.1, hvw.2⟩,
      huv.trans_le hvw.1⟩
  have hc : ContinuousOn (fun w => |(densityTransportCoefficient e S u w).re|) (Icc v 0) :=
    (Complex.continuous_re.comp_continuousOn
      ((Calculus.continuousOn_density_coefficient hS hout).comp
        (continuous_const.prodMk continuous_id).continuousOn (fun w hw => ⟨rfl, hw⟩))).abs
  have hsrc : IntervalIntegrable (fun w => ‖rawDensitySource e S u w‖) volume v 0 :=
    (((Calculus.continuousOn_rawDensitySource hS hout).comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun w hw => ⟨rfl, hw⟩)).norm).intervalIntegrable_of_Icc hv0
  exact (hw.norm.continuousOn_mul (by rwa [uIcc_of_le hv0])).add hsrc

end EmcsfAcExtension.Global.Exterior
