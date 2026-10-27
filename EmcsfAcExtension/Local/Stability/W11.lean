module

public import EmcsfAcExtension.Local.Stability.W11Ordinary
import EmcsfAcExtension.Local.Stability.MomentsSections
import EmcsfAcExtension.Infra.AC.Variation
import EmcsfAcExtension.Infra.Calculus.PartialsC1

/-! # Characteristic variation differences on the classical class

The ordinary derivative comparisons give total variation on each closed
characteristic section. Together with the main uniform comparison these
are the local strong W¹,¹ estimates consumed by the Limit layer.
The four full general-AC records remain in internal project record (internal project record).
-/

public section

open Set MeasureTheory Filter
open scoped ENNReal

namespace EmcsfAcExtension.Local

private theorem variation_eq_lintegral_section_aux {f g : ℝ → ℂ} {a b : ℝ}
    (hab : a ≤ b) (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : ContinuousOn g (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt f (g t) t) :
    eVariationOn f (Icc a b) = ∫⁻ t in Icc a b, ‖g t‖ₑ := by
  have hgi := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hab hg
  rw [hf.eVariationOn_eq_integral_norm_deriv hab]
  have hEq : (∫ t in a..b, ‖deriv f t‖) = ∫ t in a..b, ‖g t‖ := by
    apply intervalIntegral.integral_congr_ae
    have hna : ∀ᵐ t : ℝ, t ≠ a := by simp [ae_iff, measure_singleton]
    have hnb : ∀ᵐ t : ℝ, t ≠ b := by simp [ae_iff, measure_singleton]
    filter_upwards [hna, hnb] with t hta htb ht
    have ht' : t ∈ Icc a b := by
      rw [uIoc_of_le hab] at ht
      exact ⟨ht.1.le, ht.2⟩
    rw [(hd t ⟨lt_of_le_of_ne ht'.1 hta.symm, lt_of_le_of_ne ht'.2 htb⟩).deriv]
  rw [hEq, intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  exact ofReal_integral_norm_eq_lintegral_enorm
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).1 hgi)

/-- The outgoing variation of a classical normalized-field difference is
exactly the integral of its domain partial difference. There are no
estimate constants or additional smallness assumptions. -/
theorem stab_out_variation_difference_eq_lintegral_c1
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) {u : ℝ} (hu : u ∈ Icc 0 T) :
    eVariationOn (fun v => S₁.a u v - S₂.a u v) (Icc u T) =
      ∫⁻ v in Icc u T, ‖pdV (triangle 0 T) S₁.a u v - pdV (triangle 0 T) S₂.a u v‖ₑ := by
  have hmap : MapsTo (fun v : ℝ => (u, v)) (Icc u T) (triangle 0 T) :=
    fun v hv => ⟨hu.1, hv.1, hv.2⟩
  have cA₁ := (stab_normalized_out_c1 h₁s.c1).comp
    (contDiffOn_const.prodMk contDiffOn_id) hmap
  have cA₂ := (stab_normalized_out_c1 h₂s.c1).comp
    (contDiffOn_const.prodMk contDiffOn_id) hmap
  have hAC : AbsolutelyContinuousOnInterval (fun v => S₁.a u v - S₂.a u v) u T := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    rw [uIcc_of_le hu.2]
    exact cA₁.sub cA₂
  have cP := ((continuousOn_partial_v (stab_normalized_out_c1 h₁s.c1)
    (uniqueDiffOn_triangle h₁s.pos)).sub
      (continuousOn_partial_v (stab_normalized_out_c1 h₂s.c1)
        (uniqueDiffOn_triangle h₂s.pos))).comp
          (continuous_const.prodMk continuous_id).continuousOn hmap
  apply variation_eq_lintegral_section_aux hu.2 hAC cP
  intro v hv
  exact (((hasDerivWithinAt_uncurry_triangle_v (stab_normalized_out_c1 h₁s.c1)
    (hmap ⟨hv.1.le, hv.2.le⟩)).sub
      (hasDerivWithinAt_uncurry_triangle_v (stab_normalized_out_c1 h₂s.c1)
        (hmap ⟨hv.1.le, hv.2.le⟩))).hasDerivAt (Icc_mem_nhds hv.1 hv.2))

/-- The incoming ordinary variation of a classical normalized-field difference
is exactly its domain partial-difference integral. The formula uses the
ordinary connection subtraction and has coefficient one. -/
theorem stab_in_variation_difference_eq_lintegral_c1
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) {v : ℝ} (hv : v ∈ Icc 0 T) :
    eVariationOn (fun u => S₁.b u v - S₂.b u v) (Icc 0 v) =
      ∫⁻ u in Icc 0 v, ‖pdU (triangle 0 T) S₁.b u v - pdU (triangle 0 T) S₂.b u v‖ₑ := by
  have hmap : MapsTo (fun u : ℝ => (u, v)) (Icc 0 v) (triangle 0 T) :=
    fun u hu => ⟨hu.1, hu.2, hv.2⟩
  have cB₁ := (stab_normalized_in_c1 h₁s.c1).comp
    (contDiffOn_id.prodMk contDiffOn_const) hmap
  have cB₂ := (stab_normalized_in_c1 h₂s.c1).comp
    (contDiffOn_id.prodMk contDiffOn_const) hmap
  have hAC : AbsolutelyContinuousOnInterval (fun u => S₁.b u v - S₂.b u v) 0 v := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    rw [uIcc_of_le hv.1]
    exact cB₁.sub cB₂
  have cP := ((continuousOn_partial_u (stab_normalized_in_c1 h₁s.c1)
    (uniqueDiffOn_triangle h₁s.pos)).sub
      (continuousOn_partial_u (stab_normalized_in_c1 h₂s.c1)
        (uniqueDiffOn_triangle h₂s.pos))).comp
          (continuous_id.prodMk continuous_const).continuousOn hmap
  apply variation_eq_lintegral_section_aux hv.1 hAC cP
  intro u hu
  exact (((hasDerivWithinAt_uncurry_triangle_u (stab_normalized_in_c1 h₁s.c1)
    (hmap ⟨hu.1.le, hu.2.le⟩)).sub
      (hasDerivWithinAt_uncurry_triangle_u (stab_normalized_in_c1 h₂s.c1)
        (hmap ⟨hu.1.le, hu.2.le⟩))).hasDerivAt (Icc_mem_nhds hu.1 hu.2))

/-- [internal]
Local C¹ comparison for the full general-AC node
`restart-sec-bv-stability-independent#scalar-characteristic-strong-W11`.
The conclusion is the quantitative characteristic variation difference;
combined with the main uniform bound it gives strong characteristic W¹,¹
Cauchy estimates. Threshold and constant depend only on `A` and its uniform
main constant `C₀`, before all field parameters, data and derivative suprema.
The main Lipschitz input is explicit pending internal project record. -/
theorem Stab.scalar_characteristic_strong_W11_of_main_lipschitz_c1
    (A C₀ : ℝ) (hA : 0 < A) (hC₀ : 0 < C₀) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
      ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
        StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
        ε ^ 2 + sigma e M T ≤ η →
        jDist T S₁ S₂ + kDist e T S₁ S₂ + geomDist T S₁ S₂ +
          supDist T S₁.a S₂.a + supDist T S₁.b S₂.b + supDist T S₁.phi S₂.phi ≤
            ENNReal.ofReal (C₀ * dataDist h₁ h₂ T) →
        (⨆ u ∈ Icc 0 T, eVariationOn (fun v => S₁.a u v - S₂.a u v) (Icc u T)) +
        (⨆ v ∈ Icc 0 T, eVariationOn (fun u => S₁.b u v - S₂.b u v) (Icc 0 v)) ≤
          ENNReal.ofReal (C * dataDist h₁ h₂ T) := by
  obtain ⟨η, C, hη, hC, hOrdinary⟩ :=
    Stab.ordinary_incoming_difference_variation_of_main_lipschitz A C₀ hA hC₀
  refine ⟨η, C, hη, hC, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ h₁s h₂s hsmall hmain
  have ho := hOrdinary T e ε M S₁ S₂ h₁ h₂ h₁s h₂s hsmall hmain
  have hOut : (⨆ u ∈ Icc 0 T,
      eVariationOn (fun v => S₁.a u v - S₂.a u v) (Icc u T)) =
      ⨆ u ∈ Icc 0 T, ∫⁻ v in Icc u T,
        ‖pdV (triangle 0 T) S₁.a u v - pdV (triangle 0 T) S₂.a u v‖ₑ := by
    apply iSup_congr
    intro u
    apply iSup_congr
    intro hu
    exact stab_out_variation_difference_eq_lintegral_c1 h₁s h₂s hu
  have hIn : (⨆ v ∈ Icc 0 T,
      eVariationOn (fun u => S₁.b u v - S₂.b u v) (Icc 0 v)) =
      ⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v,
        ‖pdU (triangle 0 T) S₁.b u v - pdU (triangle 0 T) S₂.b u v‖ₑ := by
    apply iSup_congr
    intro v
    apply iSup_congr
    intro hv
    exact stab_in_variation_difference_eq_lintegral_c1 h₁s h₂s hv
  rwa [hOut, hIn]

end EmcsfAcExtension.Local
