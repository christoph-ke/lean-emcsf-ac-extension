module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.PotentialZeroExtension
import EmcsfAcExtension.Infra.Density.ParamIntegral

/-! # Differentiating the zero-axis potential primitive

A continuous incoming density representative gives an exact rectangle
primitive after zero extension. Fubini and the AC parameter-integral
FTC differentiate the moving-axis outgoing integral, including its
complete incoming section.
-/

public section

open Set MeasureTheory Filter
open scoped Topology

namespace EmcsfAcExtension.Local

/-- [internal]
A continuous triangle density vanishing on the axis has an outgoing
primitive which is AC in the incoming label. Its incoming derivative
is the outgoing integral of the continuous incoming density, a.e. on
every section. The exact coefficient is one; no quantitative derivative
or minimum-radius bound is used in this regularity statement. -/
theorem stab_incoming_derivative_of_triangle_primitive
    {T : ℝ} {F G H : ℝ → ℝ → ℝ}
    (cG : ContinuousOn (Function.uncurry G) (triangle 0 T))
    (cH : ContinuousOn (Function.uncurry H) (triangle 0 T))
    (haxis : ∀ t ∈ Icc 0 T, G t t = 0)
    (hd : ∀ u v, 0 ≤ u → u < v → v ≤ T →
      HasDerivWithinAt (fun s => G s v) (H u v) (Icc 0 v) u)
    (hF : ∀ u v, (u, v) ∈ triangle 0 T → F u v = ∫ w in u..v, G u w)
    {v : ℝ} (hv : v ∈ Icc 0 T) :
    AbsolutelyContinuousOnInterval (fun u => F u v) 0 v ∧
      ∀ᵐ u ∂volume.restrict (Icc 0 v),
        HasDerivAt (fun t => F t v) (∫ w in u..v, H u w) u := by
  let ZG := fun u w => (triangle 0 T).indicator (Function.uncurry G) (u, w)
  let ZH := fun u w => (triangle 0 T).indicator (Function.uncurry H) (u, w)
  have hIH : IntegrableOn (Function.uncurry H) (triangle 0 T) (volume : Measure (ℝ × ℝ)) :=
    ContinuousOn.integrableOn_compact (isCompact_triangle 0 T) cH
  have hIZ : Integrable ((triangle 0 T).indicator (Function.uncurry H)) (volume : Measure (ℝ × ℝ))
      :=
    (integrable_indicator_iff (measurableSet_triangle 0 T)).2 hIH
  rw [Measure.volume_eq_prod] at hIZ
  have hRect : Integrable (Function.uncurry ZH)
      ((volume.restrict (Icc 0 v)).prod (volume.restrict (Icc 0 v))) :=
    hIZ.mono_measure (Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self)
  have hY₀ : IntegrableOn (ZG 0) (Icc 0 v) := by
    have hm : MapsTo (fun w : ℝ => (0, w)) (Icc 0 v) (triangle 0 T) :=
      fun w hw => ⟨le_rfl, hw.1, hw.2.trans hv.2⟩
    have cg : ContinuousOn (G 0) (Icc 0 v) := cG.comp
      (continuous_const.prodMk continuous_id).continuousOn hm
    apply cg.integrableOn_Icc.congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with w hw
    dsimp only [ZG]
    rw [indicator_of_mem (hm hw)]
    rfl
  have hRep : ∀ u ∈ Icc 0 v,
      ZG u =ᵐ[volume.restrict (Icc 0 v)] (fun w => ZG 0 w + ∫ s in 0..u, ZH s w) := by
    intro u hu
    filter_upwards [ae_restrict_mem measurableSet_Icc] with w hw
    exact stab_triangle_zero_extension_incoming_primitive cG cH haxis hd
      ⟨hu.1, hu.2.trans hv.2⟩ ⟨hw.1, hw.2.trans hv.2⟩
  obtain ⟨hAC, hDeriv⟩ :=
      Global.Density.absolutelyContinuousOnInterval_parameterIntegral_of_representation
    hv.1 hRect hY₀ hRep
  have hEq u (hu : u ∈ Icc 0 v) : (∫ w in Icc 0 v, ZG u w) = F u v := by
    exact (stab_triangle_zero_extension_outgoing_integral G hu.1 hu.2 hv.2).trans
      (hF u v ⟨hu.1, hu.2, hv.2⟩).symm
  refine ⟨hAC.congr (fun u hu => hEq u (by rwa [uIcc_of_le hv.1] at hu)), ?_⟩
  have hne₀ : ∀ᵐ u : ℝ, u ≠ 0 := by simp [ae_iff]
  have hneV : ∀ᵐ u : ℝ, u ≠ v := by simp [ae_iff]
  filter_upwards [hDeriv, ae_restrict_mem measurableSet_Icc,
    ae_restrict_of_ae hne₀, ae_restrict_of_ae hneV] with u hu hum hu0 huv
  have hui : u ∈ Ioo 0 v := ⟨lt_of_le_of_ne hum.1 hu0.symm, lt_of_le_of_ne hum.2 huv⟩
  have hh : HasDerivAt (fun t => F t v) (∫ w in Icc 0 v, ZH u w) u := by
    apply hu.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hui.1 hui.2] with t ht
    exact (hEq t (Ioo_subset_Icc_self ht)).symm
  have hInt : (∫ w in Icc 0 v, ZH u w) = ∫ w in u..v, H u w :=
    stab_triangle_zero_extension_outgoing_integral H hum.1 hum.2 hv.2
  rwa [hInt] at hh

end EmcsfAcExtension.Local
