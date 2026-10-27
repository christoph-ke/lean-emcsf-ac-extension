module

public import EmcsfAcExtension.Local.Apriori.EnvelopeCloseTransport

/-! # Passing characteristic modulus estimates to the regular axis

Only continuity of the transported field is used at the endpoints. The
coefficient and forcing need only be continuous in the interior, and the
forcing budget may initially be an infinite nonnegative integral. This
implements the endpoint argument in approved internal project record (20).
-/

public section

open Set MeasureTheory Filter Topology Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- Interior characteristic transport estimates extend to both endpoints
of the closed segment. The common factor `H` is explicit and uniform in the
segment and fields. No absolute continuity or source integrability at the
axis is assumed; an extended integral records any infinite source budget. -/
theorem characteristic_transport_enorm_le_of_interior
    {a b H : ℝ} {g c q : ℝ → ℂ}
    (hab : a < b) (hH0 : 0 ≤ H) (hg : ContinuousOn g (Icc a b))
    (hc : ContinuousOn c (Ioo a b)) (hq : ContinuousOn q (Ioo a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt g (c x * g x + q x) x)
    (hH : ∀ d t, a < d → d ≤ t → t < b →
      ∀ x ∈ Icc d t, Real.exp (∫ y in x..t, (c y).re) ≤ H) :
    ‖g b‖ₑ ≤ ENNReal.ofReal H * (‖g a‖ₑ + ∫⁻ x in Icc a b, ‖q x‖ₑ) := by
  let Q : ℝ≥0∞ := ∫⁻ x in Icc a b, ‖q x‖ₑ
  have hlocal (t : ℝ) (ht : t ∈ Ioo a b) (d : ℝ) (hd' : d ∈ Ioo a t) :
      ‖g t‖ₑ ≤ ENNReal.ofReal H * (‖g d‖ₑ + Q) := by
    have hsub : Icc d t ⊆ Ioo a b := fun x hx =>
      ⟨hd'.1.trans_le hx.1, hx.2.trans_lt ht.2⟩
    have hsub' : Icc d t ⊆ Icc a b := hsub.trans Ioo_subset_Icc_self
    have hnorm := characteristic_transport_norm_le hd'.2.le (hg.mono hsub')
      (hc.mono hsub) (hq.mono hsub)
      (fun x hx => hd x (hsub ⟨hx.1.le, hx.2.le⟩))
      (hH d t hd'.1 hd'.2.le ht.2)
    have hqi := (hq.mono hsub).intervalIntegrable_of_Icc (μ := volume) hd'.2.le
    have hq0 : 0 ≤ ∫ x in d..t, ‖q x‖ :=
      intervalIntegral.integral_nonneg hd'.2.le (fun _ _ => norm_nonneg _)
    have heq : ENNReal.ofReal (∫ x in d..t, ‖q x‖) =
        ∫⁻ x in Icc d t, ‖q x‖ₑ := by
      rw [intervalIntegral.integral_of_le hd'.2.le, ← integral_Icc_eq_integral_Ioc]
      exact ofReal_integral_norm_eq_lintegral_enorm
        ((intervalIntegrable_iff_integrableOn_Icc_of_le hd'.2.le).mp hqi)
    calc
      _ = ENNReal.ofReal ‖g t‖ := (ofReal_norm _).symm
      _ ≤ ENNReal.ofReal (H * (‖g d‖ + ∫ x in d..t, ‖q x‖)) :=
        ENNReal.ofReal_le_ofReal hnorm
      _ = ENNReal.ofReal H * (‖g d‖ₑ + ∫⁻ x in Icc d t, ‖q x‖ₑ) := by
        rw [ENNReal.ofReal_mul hH0, ENNReal.ofReal_add (norm_nonneg _) hq0,
          ofReal_norm, heq]
      _ ≤ _ := by
        apply mul_le_mul' le_rfl
        apply add_le_add le_rfl
        exact lintegral_mono_set hsub'
  have hinterior (t : ℝ) (ht : t ∈ Ioo a b) :
      ‖g t‖ₑ ≤ ENNReal.ofReal H * (‖g a‖ₑ + Q) := by
    have : NeBot (𝓝[Ioo a t] a) := left_nhdsWithin_Ioo_neBot ht.1
    have hlim : Tendsto (fun d => ‖g d‖ₑ) (𝓝[Ioo a t] a) (𝓝 ‖g a‖ₑ) :=
      ((hg a ⟨le_rfl, hab.le⟩).enorm.mono (fun d hd' =>
        ⟨hd'.1.le, hd'.2.le.trans ht.2.le⟩))
    have hm : Tendsto (fun d => ENNReal.ofReal H * (‖g d‖ₑ + Q))
        (𝓝[Ioo a t] a) (𝓝 (ENNReal.ofReal H * (‖g a‖ₑ + Q))) :=
      (ENNReal.continuous_const_mul
        (a := ENNReal.ofReal H) ENNReal.ofReal_ne_top).continuousAt.tendsto.comp
          (hlim.add tendsto_const_nhds)
    apply ge_of_tendsto hm
    filter_upwards [self_mem_nhdsWithin] with d hd'
    exact hlocal t ht d hd'
  have : NeBot (𝓝[Ioo a b] b) := right_nhdsWithin_Ioo_neBot hab
  have hlim : Tendsto (fun t => ‖g t‖ₑ) (𝓝[Ioo a b] b) (𝓝 ‖g b‖ₑ) :=
    ((hg b ⟨hab.le, le_rfl⟩).enorm.mono Ioo_subset_Icc_self)
  apply le_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact hinterior t ht

end EmcsfAcExtension.Local
