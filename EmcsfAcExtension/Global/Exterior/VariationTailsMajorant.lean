module

public import EmcsfAcExtension.Global.Exterior.VariationTailsHistory
public import EmcsfAcExtension.Global.Exterior.DerivativeSourceAggregateTerminal
public import EmcsfAcExtension.Global.Exterior.OpticsCoefficients

/-! # The actual density-history row majorant

The real transport coefficient and the exact charged source are combined
with the actual AC variation. The constants `264`, `20480`, and their
sum `20744` are numerical and uniform in the solution, coupling, anchor,
row, and label. Source: `charged_SF_new_version.tex:L1364–L1380`, internal project record (M3).
-/

public section

open Set MeasureTheory Filter Topology Complex

namespace EmcsfAcExtension.Global.Exterior

/-- [internal] The real part of the density transport coefficient is the
negative incoming logarithmic expansion source. The electromagnetic
connection has zero real part. -/
theorem densityTransportCoefficient_re {e u v : ℝ} {S : Fields}
    (hl : S.lam u v ≠ 0) :
    (densityTransportCoefficient e S u v).re = -S.rUV u v / S.lam u v := by
  simp only [densityTransportCoefficient, sub_re, ofReal_re, mul_re, I_re, I_im,
    ofReal_im, mul_zero, zero_mul, sub_zero]
  unfold Fields.rUV
  field_simp [hl]

/-- [internal]
A uniform row coefficient bound and a source row bound imply the full
history bound. The canonical density can be anchored at any earlier proper
row. No pointwise bound on the rough outgoing derivative is assumed. -/
theorem density_history_row_le_of_coefficient
    {ui e a u v A B q : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui)) (hia : ui ≤ a) (hau : a ≤ u)
    (huv : u < v) (hv0 : v ≤ 0)
    (hcoef : ∀ w ∈ Icc v 0, |(densityTransportCoefficient e S u w).re| ≤ A)
    (hsource : (∫ w in v..0, ‖rawDensitySource e S u w‖) ≤
      B * (eVariationOn (S.a u) (Icc v 0)).toReal + q) :
    (∫ w in v..0, densityModulusHistory e S a (u, w)) ≤
      (A + B) * (eVariationOn (S.a u) (Icc v 0)).toReal + q := by
  have hmem (x : ℝ) (hx : x ∈ Icc a u) : (x, v) ∈ origDomain ui :=
    ⟨hia.trans hx.1, hx.2.trans_lt (huv.trans_le hv0), (hx.2.trans_lt huv).le, hv0⟩
  have hp (x : ℝ) (hx : x ∈ Icc a u) : x < v := hx.2.trans_lt huv
  have hw := (swept_density_row_primitive hS hau hmem hp ⟨hau, le_rfl⟩).1
  have hvar := swept_row_variation_eq_density_integral hS hau hmem hp ⟨hau, le_rfl⟩
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
  have hi := hw.norm.continuousOn_mul (by rwa [uIcc_of_le hv0])
  have hle := intervalIntegral.integral_mono_on hv0 hi (hw.norm.const_mul A)
    (fun w hw => mul_le_mul_of_nonneg_right (hcoef w hw) (norm_nonneg _))
  rw [intervalIntegral.integral_const_mul, ← hvar] at hle
  change (∫ w in v..0, |(densityTransportCoefficient e S u w).re| *
    ‖densityRepresentative e S a u w‖ + ‖rawDensitySource e S u w‖) ≤ _
  rw [intervalIntegral.integral_add hi hsrc]
  nlinarith only [hle, hsource]

/-- [internal]
The terminal consumers discharge the coefficient and source profiles
in the moving-interval history bound. The cutoff is fixed before all
rows and all anchors. The coefficient `20744=264+20480` is universal. -/
theorem density_history_majorant_of_terminal {ui e C : ℝ} {S : Fields}
    (h : OriginalData ui e S) (M ell : ℝ → ℝ)
    {R₀ : ℝ} (hR : 0 < R₀) (hC : 0 < C)
    (hcollapse : Tendsto (fun u => S.r u 0) (𝓝[<] 0) (𝓝 0))
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hell : ∀ R ∈ Ioc 0 R₀, 0 < ell R)
    (hellsmall : Tendsto (fun R => ell R / R) (𝓝[>] 0) (𝓝 0))
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0))
    (hphi : ∀ u ∈ Ico ui 0, ‖S.phi u 0‖ ≤
      C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0)))) :
    ∃ u₀ ∈ Ioo ui 0, ∀ a u v, ui ≤ a → a ≤ u → u < v →
      (u, v) ∈ adaptiveExterior S ui u₀ ell → S.r u v = ell (S.r u 0) →
      let L := fun R => (C + 2) * (1 + Real.sqrt (Real.log (S.r ui 0 / R)))
      (∫ w in v..0, densityModulusHistory e S a (u, w)) ≤
        (20744 * (-S.nu u 0) * (M (S.r u 0) / ell (S.r u 0) ^ 2)) *
          (eVariationOn (S.a u) (Icc v 0)).toReal +
        20480 * (-S.nu u 0) * exteriorForcing e M ell L (S.r u 0) := by
  obtain ⟨us, hus, hsource⟩ := source_variation_majorant_of_terminal h M ell hR hC
    hcollapse hmass hell hellsmall hsmall hphi
  obtain ⟨uo, huo, hopt⟩ := incoming_optical_majorant_of_terminal h M ell hR hC
    hcollapse hmass hell hellsmall hsmall hphi
  refine ⟨max us uo, ⟨lt_max_of_lt_left hus.1, max_lt hus.2 huo.2⟩, ?_⟩
  intro a u v hia hau huv hp hroot
  have hp0 : (u, 0) ∈ origDomain ui := ⟨hp.1.1, hp.1.2.1, hp.1.2.1.le, le_rfl⟩
  have hM := hmass u ⟨hp.1.1, hp.1.2.1⟩
  have hs := hsource u v ⟨hp.1, (le_max_left us uo).trans hp.2.1, hp.2.2⟩ hroot
  have heq : (264 * (-S.nu u 0) * (M (S.r u 0) / ell (S.r u 0) ^ 2) +
      20480 * (-S.nu u 0) * (M (S.r u 0) / ell (S.r u 0) ^ 2)) =
      20744 * (-S.nu u 0) * (M (S.r u 0) / ell (S.r u 0) ^ 2) := by ring
  rw [← heq]
  apply density_history_row_le_of_coefficient h.solution hia hau huv hp.1.2.2.2
  · intro w hw
    have hsrow : outSeg u v 0 ⊆ origDomain ui :=
      (outSeg_subset_origDomain_iff hp.1.2.2.2).2
        ⟨hp.1.1, hp.1.2.1, huv.le, le_rfl⟩
    have hrad := outgoing_radius_mono h huv.le hw.1
      (fun _ hx => hsrow (outSeg_subset_outSeg le_rfl hw.2 hx))
    have hpw : (u, w) ∈ adaptiveExterior S ui uo ell :=
      ⟨hsrow ⟨rfl, hw⟩, (le_max_right us uo).trans hp.2.1, hp.2.2.trans hrad⟩
    rw [densityTransportCoefficient_re (h.solution.lam_pos (u, w) hpw.1).ne',
      neg_div, abs_neg]
    have ho := (hopt (u, w) hpw).2
    rw [terminalMass_def, terminalRadius_def, ← hM] at ho
    simpa only [div_eq_mul_inv, mul_assoc] using ho
  · nlinarith only [hs]

end EmcsfAcExtension.Global.Exterior
