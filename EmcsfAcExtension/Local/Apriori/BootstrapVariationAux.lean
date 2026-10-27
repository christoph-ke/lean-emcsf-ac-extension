module

public import EmcsfAcExtension.Local.Defs.Partial
public import EmcsfAcExtension.Frozen.Triangle
import EmcsfAcExtension.Local.Calculus.Partials
import EmcsfAcExtension.Infra.AC.Variation

/-! # Variation identities for classical characteristic restrictions

Both identities use the canonical within-triangle partial on the complete
closed section. The endpoint values of ordinary derivatives are removed
only on null sets, and the curve itself keeps its actual endpoint values.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Local

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The outgoing variation of a C¹ field is exactly the integral of the
norm of its canonical outgoing partial. The coefficient one is uniform in
all intervals and fields, with no uniform derivative bound assumed. -/
theorem variation_out_eq_integral_partial {T : ℝ} {f : ℝ → ℝ → E}
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    eVariationOn (f u) (Icc u v) = ENNReal.ofReal (∫ x in u..v, ‖pdV (triangle 0 T) f u x‖) := by
  have hs : MapsTo (fun x : ℝ => (u, x)) (Icc u v) (triangle 0 T) :=
    fun x hx => ⟨hu, hx.1, hx.2.trans hvT⟩
  have cf : ContDiffOn ℝ 1 (f u) (Icc u v) :=
    hf.comp (contDiffOn_const.prodMk contDiffOn_id) hs
  have hac : AbsolutelyContinuousOnInterval (f u) u v := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le huv] using cf
  rw [hac.eVariationOn_eq_integral_norm_deriv huv]
  congr 1
  apply intervalIntegral.integral_congr_ae
  have ha : ∀ᵐ x : ℝ, x ≠ u := by simp [ae_iff, measure_singleton]
  have hb : ∀ᵐ x : ℝ, x ≠ v := by simp [ae_iff, measure_singleton]
  filter_upwards [ha, hb] with x hxa hxb hx
  rw [uIoc_of_le huv] at hx
  have hd := (hasDerivWithinAt_pdV hf (hs ⟨hx.1.le, hx.2⟩) hs).hasDerivAt
    (Icc_mem_nhds hx.1 (lt_of_le_of_ne hx.2 hxb))
  rw [hd.deriv]

/-- The incoming variation of a C¹ field is exactly the integral of the
norm of its canonical incoming partial. The coefficient one is uniform
in all intervals and fields, including zero-length sections. -/
theorem variation_in_eq_integral_partial {T : ℝ} {f : ℝ → ℝ → E}
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    eVariationOn (fun x => f x v) (Icc u v) =
      ENNReal.ofReal (∫ x in u..v, ‖pdU (triangle 0 T) f x v‖) := by
  have hs : MapsTo (fun x : ℝ => (x, v)) (Icc u v) (triangle 0 T) :=
    fun x hx => ⟨hu.trans hx.1, hx.2, hvT⟩
  have cf : ContDiffOn ℝ 1 (fun x => f x v) (Icc u v) :=
    hf.comp (contDiffOn_id.prodMk contDiffOn_const) hs
  have hac : AbsolutelyContinuousOnInterval (fun x => f x v) u v := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le huv] using cf
  rw [hac.eVariationOn_eq_integral_norm_deriv huv]
  congr 1
  apply intervalIntegral.integral_congr_ae
  have ha : ∀ᵐ x : ℝ, x ≠ u := by simp [ae_iff, measure_singleton]
  have hb : ∀ᵐ x : ℝ, x ≠ v := by simp [ae_iff, measure_singleton]
  filter_upwards [ha, hb] with x hxa hxb hx
  rw [uIoc_of_le huv] at hx
  have hd := (hasDerivWithinAt_pdU hf (hs ⟨hx.1.le, hx.2⟩) hs).hasDerivAt
    (Icc_mem_nhds hx.1 (lt_of_le_of_ne hx.2 hxb))
  rw [hd.deriv]

end EmcsfAcExtension.Local
