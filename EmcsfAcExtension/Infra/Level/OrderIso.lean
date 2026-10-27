module

public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Order.MonotoneContinuity
public import Mathlib.Order.Hom.Set
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft

/-!
# Canonical inverses of radius labels

Increasing row radii and decreasing terminal radii are inverted on their actual
images. The inverse is the inverse of an order isomorphism between subtypes;
there is no extension outside the image. Closed intervals include both endpoints,
and the image construction also applies to half-open and disconnected domains.
-/

public section

open Set
open Filter
open scoped Topology

namespace EmcsfAcExtension.Global.Level

/-- [internal] A strictly increasing label, with its specified image, as an order isomorphism. -/
noncomputable def orderIsoOn_of_image_eq {f : ℝ → ℝ} {s t : Set ℝ}
    (hm : StrictMonoOn f s) (hi : f '' s = t) : s ≃o t :=
  (hm.orderIso f s).trans (Set.orderIsoOfEq _ _ hi)

/-- [internal] The forward map of the image order isomorphism is the original label. -/
@[simp] theorem orderIsoOn_of_image_eq_apply {f : ℝ → ℝ} {s t : Set ℝ}
    (hm : StrictMonoOn f s) (hi : f '' s = t) (x : s) :
    (orderIsoOn_of_image_eq hm hi x : ℝ) = f x := by
  change (hm.injOn.bijOn_image.equiv f x).val = f x
  simp [Set.BijOn.equiv]

/-- [internal] A strictly decreasing label reverses the order on its domain.
The inverse is defined only on the specified image. -/
noncomputable def orderIsoOnAnti_of_image_eq {f : ℝ → ℝ} {s t : Set ℝ}
    (hm : StrictAntiOn f s) (hi : f '' s = t) : sᵒᵈ ≃o t where
  toEquiv := (hm.injOn.bijOn_image.equiv _).trans (Set.equivOfEq hi)
  map_rel_iff' := by
    intro x y
    exact hm.le_iff_ge x.ofDual.property y.ofDual.property

/-- [internal] The decreasing image isomorphism evaluates to the original label. -/
@[simp] theorem orderIsoOnAnti_of_image_eq_apply {f : ℝ → ℝ} {s t : Set ℝ}
    (hm : StrictAntiOn f s) (hi : f '' s = t) (x : sᵒᵈ) :
    (orderIsoOnAnti_of_image_eq hm hi x : ℝ) = f x.ofDual := by
  change (hm.injOn.bijOn_image.equiv f x.ofDual).val = f x.ofDual
  simp [Set.BijOn.equiv]

/-- [internal] Canonical increasing compact-interval label. No nondegeneracy is required. -/
noncomputable def intervalOrderIso {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn f (Icc a b)) (hm : StrictMonoOn f (Icc a b)) :
    Icc a b ≃o Icc (f a) (f b) :=
  orderIsoOn_of_image_eq hm (hc.image_Icc_of_monotoneOn hab hm.monotoneOn)

/-- [internal] Canonical decreasing compact-interval label, with the source order reversed. -/
noncomputable def intervalOrderIsoAnti {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn f (Icc a b)) (hm : StrictAntiOn f (Icc a b)) :
    (Icc a b)ᵒᵈ ≃o Icc (f b) (f a) :=
  orderIsoOnAnti_of_image_eq hm (hc.image_Icc_of_antitoneOn hab hm.antitoneOn)

/-- [internal] The increasing interval isomorphism evaluates to the original map. -/
@[simp] theorem intervalOrderIso_apply {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn f (Icc a b)) (hm : StrictMonoOn f (Icc a b)) (x : Icc a b) :
    (intervalOrderIso hab hc hm x : ℝ) = f x := by
  simp [intervalOrderIso]

/-- [internal] The decreasing interval isomorphism evaluates to the original map. -/
@[simp] theorem intervalOrderIsoAnti_apply {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn f (Icc a b)) (hm : StrictAntiOn f (Icc a b))
    (x : (Icc a b)ᵒᵈ) :
    (intervalOrderIsoAnti hab hc hm x : ℝ) = f x.ofDual := by
  simp [intervalOrderIsoAnti]

/-- [internal] The image of a decreasing terminal label with a finite missing
endpoint limit is exactly the expected half-open radius interval. The lower
bound is strict at every existing point; no value at the missing endpoint occurs. -/
theorem image_Ico_of_strictAntiOn_tendsto {f : ℝ → ℝ} {a b L : ℝ}
    (hab : a < b) (hc : ContinuousOn f (Ico a b)) (hm : StrictAntiOn f (Ico a b))
    (hL : ∀ x ∈ Ico a b, L < f x) (ht : Tendsto f (𝓝[<] b) (𝓝 L)) :
    f '' Ico a b = Ioc L (f a) := by
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨hL x hx, hm.antitoneOn ⟨le_rfl, hab⟩ hx hx.1⟩
  · exact isPreconnected_Ico.intermediate_value_Ioc ⟨le_rfl, hab⟩
      (le_principal_iff.mpr (Ico_mem_nhdsLT hab)) hc ht

/-- [internal] Canonical inverse for a decreasing terminal radius on a half-open
label interval, with finite limiting radius `L`. -/
noncomputable def terminalOrderIso {f : ℝ → ℝ} {a b L : ℝ}
    (hab : a < b) (hc : ContinuousOn f (Ico a b)) (hm : StrictAntiOn f (Ico a b))
    (hL : ∀ x ∈ Ico a b, L < f x) (ht : Tendsto f (𝓝[<] b) (𝓝 L)) :
    (Ico a b)ᵒᵈ ≃o Ioc L (f a) :=
  orderIsoOnAnti_of_image_eq hm (image_Ico_of_strictAntiOn_tendsto hab hc hm hL ht)

/-- [internal] The terminal-radius isomorphism evaluates to the original radius. -/
@[simp] theorem terminalOrderIso_apply {f : ℝ → ℝ} {a b L : ℝ}
    (hab : a < b) (hc : ContinuousOn f (Ico a b)) (hm : StrictAntiOn f (Ico a b))
    (hL : ∀ x ∈ Ico a b, L < f x) (ht : Tendsto f (𝓝[<] b) (𝓝 L))
    (x : (Ico a b)ᵒᵈ) : (terminalOrderIso hab hc hm hL ht x : ℝ) = f x.ofDual := by
  simp [terminalOrderIso]

/-- [internal] The real representative of an interval isomorphism's inverse.
Outside the image it has the constant endpoint extension `IccExtend`; all inverse
identities below are asserted on the image. There is no arbitrary off-range choice. -/
@[expose] noncomputable def intervalInverse {a b c d : ℝ} (e : Icc a b ≃o Icc c d) (hcd : c ≤ d) :
    ℝ → ℝ := IccExtend hcd (fun t => (e.symm t : ℝ))

/-- [internal] The real inverse agrees with the subtype inverse on its image. -/
@[simp] theorem intervalInverse_apply {a b c d : ℝ} (e : Icc a b ≃o Icc c d)
    (hcd : c ≤ d) (t : Icc c d) : intervalInverse e hcd t = (e.symm t : ℝ) := by
  simp [intervalInverse, IccExtend_val]

/-- [internal] The real inverse followed by the original interval isomorphism
recovers each source point, including its endpoints. -/
@[simp] theorem intervalInverse_apply_apply {a b c d : ℝ} (e : Icc a b ≃o Icc c d)
    (hcd : c ≤ d) (x : Icc a b) : intervalInverse e hcd (e x) = x := by
  simp

/-- [internal] The canonical real inverse is continuous on the whole real line. -/
theorem continuous_intervalInverse {a b c d : ℝ} (e : Icc a b ≃o Icc c d)
    (hcd : c ≤ d) : Continuous (intervalInverse e hcd) := by
  unfold intervalInverse
  exact (continuous_subtype_val.comp e.symm.continuous).Icc_extend'

/-- [internal] The real inverse always takes values in the source interval. -/
theorem intervalInverse_mem {a b c d : ℝ} (e : Icc a b ≃o Icc c d) (hcd : c ≤ d)
    (t : ℝ) : intervalInverse e hcd t ∈ Icc a b := by
  simpa only [intervalInverse, IccExtend, Function.comp_apply] using
    (e.symm (projIcc c d hcd t)).property

/-- [internal] The derivative of a canonical interval inverse, including
one-sided derivatives at the endpoints. The hypothesis identifies the forward
map and supplies its nonzero derivative at the inverse point. -/
theorem hasDerivWithinAt_intervalInverse_of_deriv {a b c d t q : ℝ}
    {f : ℝ → ℝ} (e : Icc a b ≃o Icc c d) (hcd : c ≤ d)
    (he : ∀ x : Icc a b, (e x : ℝ) = f x) (ht : t ∈ Icc c d)
    (hd : HasDerivWithinAt f q (Icc a b) (intervalInverse e hcd t)) (hq : q ≠ 0) :
    HasDerivWithinAt (intervalInverse e hcd) q⁻¹ (Icc c d) t := by
  have hmap : MapsTo (intervalInverse e hcd) (Icc c d) (Icc a b) :=
    fun x _ => intervalInverse_mem e hcd x
  have hi : ∀ x ∈ Icc c d, f (intervalInverse e hcd x) = x := by
    intro x hx
    have h := congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)
    simpa only [he, ← intervalInverse_apply e hcd ⟨x, hx⟩] using h
  have hlim : Tendsto (intervalInverse e hcd) (𝓝[Icc c d] t)
      (𝓝[Icc a b] (intervalInverse e hcd t)) :=
    (continuous_intervalInverse e hcd).continuousAt.continuousWithinAt.tendsto_nhdsWithin hmap
  have hcomp : f ∘ intervalInverse e hcd =ᶠ[𝓝[Icc c d] t] id := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hi x hx
  have h := HasFDerivWithinAt.of_comp_of_leftInverse hlim hd.hasFDerivWithinAt
    (hasFDerivWithinAt_id t (Icc c d)) hcomp
    (f'symm := ContinuousLinearMap.toSpanSingleton ℝ q⁻¹) (fun x => by simp [hq]) ht
  simpa using h.hasDerivWithinAt

end EmcsfAcExtension.Global.Level
