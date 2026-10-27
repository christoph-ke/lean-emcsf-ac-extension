/- Copyright (c) 2026. All rights reserved. -/
module

public import EmcsfAcExtension.Frozen.IsSolution
public import EmcsfAcExtension.Infra.Null.IntegralForm
public import EmcsfAcExtension.Global.Api.Domains
import EmcsfAcExtension.Local.Calculus.Sections
import EmcsfAcExtension.Infra.BV.Basic

/-! # Sectional calculus before and at an existing endpoint

The frozen local calculus supplies the equations off the axis. Here a countable
cover identifies their derivatives on an open section. BV then gives density
integrability, and continuity passes the primitive identity to both endpoints.
This argument does not infer AC from a general continuous BV limit.
-/

public section

open Set MeasureTheory Filter Topology

namespace EmcsfAcExtension.Global.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f g : ℝ → E} {a b : ℝ}

/-- [internal] Anchored integral equations identify the a.e. sectional derivative. -/
theorem ac_ae_of_integralForm_on [FiniteDimensional ℝ E] (hab : a ≤ b)
    (h : ∀ x ∈ Icc a b, IntegralForm f g a x) :
    AbsolutelyContinuousOnInterval f a b ∧
      ∀ᵐ x ∂volume.restrict (Icc a b), HasDerivAt f (g x) x := by
  refine ⟨absolutelyContinuousOnInterval_of_integralForm_on hab h, ?_⟩
  rw [← restrict_Ioo_eq_restrict_Icc]
  filter_upwards [ae_restrict_of_ae ((h b ⟨hab, le_rfl⟩).1.ae_hasDerivAt_integral),
    ae_restrict_mem measurableSet_Ioo] with x hx hmem
  have hx' : x ∈ uIcc a b := by
    simpa only [uIcc_of_le hab] using Ioo_subset_Icc_self hmem
  apply ((hx hx' a left_mem_uIcc).const_add (f a)).congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds hmem.1 hmem.2] with y hy
  exact (h y hy).eq_add_integral

/-- [internal] Integral equations on all proper interior sections identify the
ordinary derivative a.e.; endpoint values of the density are irrelevant. -/
theorem ae_hasDerivAt_of_local_integralForm [FiniteDimensional ℝ E]
    (h : ∀ c ∈ Ioo a b, ∀ d ∈ Ioo a b, c ≤ d → IntegralForm f g c d) :
    ∀ᵐ x ∂volume.restrict (Icc a b), HasDerivAt f (g x) x := by
  have hall : ∀ᵐ x : ℝ, ∀ q r : ℚ, a < (q : ℝ) → (r : ℝ) < b →
      (q : ℝ) ≤ r → x ∈ Icc (q : ℝ) r → HasDerivAt f (g x) x := by
    simp only [ae_all_iff]
    intro q r hq hr hqr
    apply (ae_restrict_iff' measurableSet_Icc).1
    exact (ac_ae_of_integralForm_on hqr (fun y hy =>
      h q ⟨hq, hqr.trans_lt hr⟩ y ⟨hq.trans_le hy.1, hy.2.trans_lt hr⟩ hy.1)).2
  rw [← restrict_Ioo_eq_restrict_Icc]
  filter_upwards [ae_restrict_of_ae hall, ae_restrict_mem measurableSet_Ioo] with x hx hmem
  obtain ⟨q, haq, hqx⟩ := exists_rat_btwn hmem.1
  obtain ⟨r, hxr, hrb⟩ := exists_rat_btwn hmem.2
  exact hx q r haq hrb (hqx.trans hxr).le ⟨hqx.le, hxr.le⟩

/-- [internal] Finite characteristic variation proves integrability of the actual
equation source, after its a.e. identification on proper interior sections. -/
theorem intervalIntegrable_of_bv_of_local_integralForm [FiniteDimensional ℝ E] (hab : a ≤ b)
    (hf : BoundedVariationOn f (Icc a b))
    (h : ∀ c ∈ Ioo a b, ∀ d ∈ Ioo a b, c ≤ d → IntegralForm f g c d) :
    IntervalIntegrable g volume a b := by
  have he : deriv f =ᵐ[volume.restrict (Icc a b)] g :=
    (ae_hasDerivAt_of_local_integralForm h).mono fun _ hx => hx.deriv
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2
  exact ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).1
    (hf.intervalIntegrable_deriv_finiteDimensional hab)).congr he

/-- [internal] A continuous section with integrable density satisfies the same
integral equation at both endpoints as on every interior subinterval. -/
theorem integralForm_of_continuousOn_of_local_integralForm_of_intervalIntegrable
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hg : IntervalIntegrable g volume a b)
    (h : ∀ c ∈ Ioo a b, ∀ d ∈ Ioo a b, c ≤ d → IntegralForm f g c d) :
    IntegralForm f g a b := by
  rcases hab.eq_or_lt with rfl | hab
  · exact integralForm_self f g a
  let P (x : ℝ) := f x - ∫ t in a..x, g t
  have hc : ContinuousOn P (Icc a b) := hf.sub (by
    simpa only [uIcc_of_le hab.le] using
      (hg.absolutelyContinuousOnInterval_intervalIntegral_normed left_mem_uIcc).continuousOn)
  have hp {c d : ℝ} (hc : c ∈ Ioo a b) (hd : d ∈ Ioo a b) (hcd : c ≤ d) :
      P c = P d := by
    have hcg := hg.mono_set (uIcc_subset_uIcc left_mem_uIcc (Icc_subset_uIcc ⟨hc.1.le, hc.2.le⟩))
    have hdg := hg.mono_set (uIcc_subset_uIcc left_mem_uIcc (Icc_subset_uIcc ⟨hd.1.le, hd.2.le⟩))
    have he := (h c hc d hd hcd).2
    have hi := intervalIntegral.integral_interval_sub_left hdg hcg
    dsimp [P]
    rw [← hi] at he
    calc
      f c - (∫ t in a..c, g t) =
          f d - ((f d - f c) + ∫ t in a..c, g t) := by abel
      _ = f d - ∫ t in a..d, g t := by rw [he, sub_add_cancel]
  have hm : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  have he : EqOn P (fun _ => P ((a + b) / 2)) (Ioo a b) := by
    intro x hx
    rcases le_total x ((a + b) / 2) with hxm | hmx
    · exact hp hx hm hxm
    · exact (hp hm hx hmx).symm
  have he' := he.of_subset_closure hc continuousOn_const Ioo_subset_Icc_self
    (show Icc a b ⊆ closure (Ioo a b) by rw [closure_Ioo hab.ne])
  have ha := he' ⟨le_rfl, hab.le⟩
  have hb := he' ⟨hab.le, le_rfl⟩
  have heq := hb.trans ha.symm
  dsimp [P] at heq
  rw [intervalIntegral.integral_same, sub_zero] at heq
  refine ⟨hg, ?_⟩
  rw [sub_eq_iff_eq_add.mp heq]
  abel

/-- [internal] Local AC equations, finite variation and endpoint continuity give
the closed-section FTC with no extra integrability assumption. -/
theorem integralForm_of_continuousOn_of_bv_of_local_integralForm
    [FiniteDimensional ℝ E] (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hbv : BoundedVariationOn f (Icc a b))
    (h : ∀ c ∈ Ioo a b, ∀ d ∈ Ioo a b, c ≤ d → IntegralForm f g c d) :
    IntegralForm f g a b :=
  integralForm_of_continuousOn_of_local_integralForm_of_intervalIntegrable hab hf
    (intervalIntegrable_of_bv_of_local_integralForm hab hbv h) h

variable {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}

/-- [internal] Continuity on any domain restricts to a closed outgoing section. -/
theorem continuousOn_out_section {F : Type*} [TopologicalSpace F] {f : ℝ → ℝ → F}
    (hf : ContinuousOn (Function.uncurry f) D) {u a b : ℝ} (hs : outSeg u a b ⊆ D) :
    ContinuousOn (f u) (Icc a b) :=
  hf.comp (continuous_const.prodMk continuous_id).continuousOn
    (fun _ hx => hs ⟨rfl, hx.1, hx.2⟩)

/-- [internal] Continuity on any domain restricts to a closed incoming section. -/
theorem continuousOn_in_section {F : Type*} [TopologicalSpace F] {f : ℝ → ℝ → F}
    (hf : ContinuousOn (Function.uncurry f) D) {a b v : ℝ} (hs : inSeg a b v ⊆ D) :
    ContinuousOn (fun u => f u v) (Icc a b) :=
  hf.comp (continuous_id.prodMk continuous_const).continuousOn
    (fun _ hx => hs ⟨hx.1, hx.2, rfl⟩)

/-- [internal] Local characteristic BV gives actual finite variation of each
expansion and normalized scalar on a proper closed outgoing segment. -/
theorem bv_out_section (hS : IsSolution e S D) {u a b : ℝ} (hs : outSeg u a b ⊆ D) :
    BoundedVariationOn (S.lam u) (Icc a b) ∧
    BoundedVariationOn (S.nu u) (Icc a b) ∧
    BoundedVariationOn (S.a u) (Icc a b) ∧
    BoundedVariationOn (S.b u) (Icc a b) := by
  obtain ⟨B, hB, hout, _⟩ := hS.bv_loc _ hs (isCompact_outSeg u a b)
  obtain ⟨hl, hn, ha, hb⟩ := hout u a b Subset.rfl
  exact ⟨ne_top_of_le_ne_top hB.ne hl, ne_top_of_le_ne_top hB.ne hn,
    ne_top_of_le_ne_top hB.ne ha, ne_top_of_le_ne_top hB.ne hb⟩

/-- [internal] Local characteristic BV gives actual finite variation of each
expansion and normalized scalar on a proper closed incoming segment. -/
theorem bv_in_section (hS : IsSolution e S D) {a b v : ℝ} (hs : inSeg a b v ⊆ D) :
    BoundedVariationOn (fun u => S.lam u v) (Icc a b) ∧
    BoundedVariationOn (fun u => S.nu u v) (Icc a b) ∧
    BoundedVariationOn (fun u => S.a u v) (Icc a b) ∧
    BoundedVariationOn (fun u => S.b u v) (Icc a b) := by
  obtain ⟨B, hB, _, hin⟩ := hS.bv_loc _ hs (isCompact_inSeg a b v)
  obtain ⟨hl, hn, ha, hb⟩ := hin a b v Subset.rfl
  exact ⟨ne_top_of_le_ne_top hB.ne hl, ne_top_of_le_ne_top hB.ne hn,
    ne_top_of_le_ne_top hB.ne ha, ne_top_of_le_ne_top hB.ne hb⟩

end EmcsfAcExtension.Global.Calculus
