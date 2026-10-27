module

public import EmcsfAcExtension.Local.Defs.Partial
public import EmcsfAcExtension.Frozen.Triangle
import EmcsfAcExtension.Infra.Calculus.PartialsC1
import EmcsfAcExtension.Infra.Calculus.MixedWithin

/-! # Mixed partials recovered from a characteristic integral equation

A C¹ function is integrated in its prescribed direction on a closed rectangle.
The transverse derivative of the primitive is then differentiated by the internal project record
integral-representation theorem. No second derivative of the function is assumed.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Local

/-- Recover the incoming derivative of the outgoing partial from the incoming
transport equation, on a nondegenerate closed rectangle. The only differentiated
source is `G`; the mixed derivative of `f` is a conclusion. -/
theorem mixed_u_pdV_of_transport_aux {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {D : Set (ℝ × ℝ)} {f G Gv : ℝ → ℝ → E} {a b c d u v : ℝ}
    (hab : a < b) (hcd : c < d)
    (hrect : Icc a b ×ˢ Icc c d ⊆ D)
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) D)
    (hG : ContinuousOn (Function.uncurry (fun y t => G t y)) (Icc c d ×ˢ Icc a b))
    (hGv : ContinuousOn (Function.uncurry (fun y t => Gv t y)) (Icc c d ×ˢ Icc a b))
    (heq : ∀ x ∈ Icc a b, ∀ y ∈ Icc c d, pdU D f x y = G x y)
    (hd : ∀ y ∈ Icc c d, ∀ t ∈ Icc a b,
      HasDerivWithinAt (G t) (Gv t y) (Icc c d) y)
    (hu : u ∈ Icc a b) (hv : v ∈ Icc c d) :
    HasDerivWithinAt (fun x => pdV D f x v) (Gv u v) (Icc a b) u := by
  have hfu (x y : ℝ) (hx : x ∈ Icc a b) (hy : y ∈ Icc c d) :
      HasDerivWithinAt (fun t => f t y) (G x y) (Icc a b) x := by
    rw [← heq x hx y hy]
    exact hasDerivWithinAt_section_u hf (hrect ⟨hx, hy⟩)
      (fun t ht => hrect ⟨ht, hy⟩)
  have hfv (x y : ℝ) (hx : x ∈ Icc a b) (hy : y ∈ Icc c d) :
      HasDerivWithinAt (f x) (pdV D f x y) (Icc c d) y :=
    hasDerivWithinAt_section_v hf (hrect ⟨hx, hy⟩)
      (fun t ht => hrect ⟨hx, ht⟩)
  have hrep (x : ℝ) (hx : x ∈ Icc a b) (y : ℝ) (hy : y ∈ Icc c d) :
      f x y = f a y + ∫ t in a..x, G t y := by
    have hc := hf.continuousOn.comp (continuousOn_id.prodMk continuousOn_const)
      (s := Icc a x) (fun t ht => hrect ⟨⟨ht.1, ht.2.trans hx.2⟩, hy⟩)
    have hg := hG.comp (continuousOn_const.prodMk continuousOn_id)
      (s := Icc a x) (fun t ht => ⟨hy, ⟨ht.1, ht.2.trans hx.2⟩⟩)
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.1 hc
      (fun t ht => (hfu t y ⟨ht.1.le, ht.2.le.trans hx.2⟩ hy).hasDerivAt
        (Icc_mem_nhds ht.1 (ht.2.trans_le hx.2)))
      (hg.intervalIntegrable_of_Icc hx.1)
    change (∫ t in a..x, G t y) = f x y - f a y at hftc
    rw [hftc]
    abel
  have hB := hfv a v ⟨le_rfl, hab.le⟩ hv
  have hm := (hasDerivWithinAt_mixed_integral_primitive_rectangle hab hcd hG hGv hd
    hu hv hB).1
  have hpartial (x : ℝ) (hx : x ∈ Icc a b) :
      pdV D f x v =
        derivWithin (fun y => f a y + ∫ t in a..x, G t y) (Icc c d) v := by
    exact ((hfv x v hx hv).congr (fun y hy => (hrep x hx y hy).symm)
      (hrep x hx v hv).symm).derivWithin (uniqueDiffOn_Icc hcd v hv) |>.symm
  exact hm.congr hpartial (hpartial u hu)

/-- Recover the outgoing derivative of the incoming partial from the outgoing
transport equation. This is the second orientation of the integral argument,
including parameter and integration endpoints of the closed rectangle. -/
theorem mixed_v_pdU_of_transport_aux {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {D : Set (ℝ × ℝ)} {f G Gu : ℝ → ℝ → E} {a b c d u v : ℝ}
    (hab : a < b) (hcd : c < d)
    (hrect : Icc a b ×ˢ Icc c d ⊆ D)
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) D)
    (hG : ContinuousOn (Function.uncurry G) (Icc a b ×ˢ Icc c d))
    (hGu : ContinuousOn (Function.uncurry Gu) (Icc a b ×ˢ Icc c d))
    (heq : ∀ x ∈ Icc a b, ∀ y ∈ Icc c d, pdV D f x y = G x y)
    (hd : ∀ x ∈ Icc a b, ∀ t ∈ Icc c d,
      HasDerivWithinAt (fun z => G z t) (Gu x t) (Icc a b) x)
    (hu : u ∈ Icc a b) (hv : v ∈ Icc c d) :
    HasDerivWithinAt (fun y => pdU D f u y) (Gu u v) (Icc c d) v := by
  have hfv (x y : ℝ) (hx : x ∈ Icc a b) (hy : y ∈ Icc c d) :
      HasDerivWithinAt (f x) (G x y) (Icc c d) y := by
    rw [← heq x hx y hy]
    exact hasDerivWithinAt_section_v hf (hrect ⟨hx, hy⟩)
      (fun t ht => hrect ⟨hx, ht⟩)
  have hfu (x y : ℝ) (hx : x ∈ Icc a b) (hy : y ∈ Icc c d) :
      HasDerivWithinAt (fun t => f t y) (pdU D f x y) (Icc a b) x :=
    hasDerivWithinAt_section_u hf (hrect ⟨hx, hy⟩)
      (fun t ht => hrect ⟨ht, hy⟩)
  have hrep (x : ℝ) (hx : x ∈ Icc a b) (y : ℝ) (hy : y ∈ Icc c d) :
      f x y = f x c + ∫ t in c..y, G x t := by
    have hc := hf.continuousOn.comp (continuousOn_const.prodMk continuousOn_id)
      (s := Icc c y) (fun t ht => hrect ⟨hx, ⟨ht.1, ht.2.trans hy.2⟩⟩)
    have hg := hG.comp (continuousOn_const.prodMk continuousOn_id)
      (s := Icc c y) (fun t ht => ⟨hx, ⟨ht.1, ht.2.trans hy.2⟩⟩)
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hy.1 hc
      (fun t ht => (hfv x t hx ⟨ht.1.le, ht.2.le.trans hy.2⟩).hasDerivAt
        (Icc_mem_nhds ht.1 (ht.2.trans_le hy.2)))
      (hg.intervalIntegrable_of_Icc hy.1)
    change (∫ t in c..y, G x t) = f x y - f x c at hftc
    rw [hftc]
    abel
  have hB := hfu u c hu ⟨le_rfl, hcd.le⟩
  have hm := (hasDerivWithinAt_mixed_integral_primitive_rectangle hcd hab hG hGu hd
    hv hu hB).1
  have hpartial (y : ℝ) (hy : y ∈ Icc c d) :
      pdU D f u y =
        derivWithin (fun x => f x c + ∫ t in c..y, G x t) (Icc a b) u := by
    exact ((hfu u y hu hy).congr (fun x hx => (hrep x hx y hy).symm)
      (hrep u hu y hy).symm).derivWithin (uniqueDiffOn_Icc hab u hu) |>.symm
  exact hm.congr hpartial (hpartial v hv)

end EmcsfAcExtension.Local
