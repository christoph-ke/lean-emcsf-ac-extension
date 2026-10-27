module

public import EmcsfAcExtension.Frozen.IsSolution
import EmcsfAcExtension.Infra.Null.IntegralForm
import EmcsfAcExtension.Infra.Calculus.SectionalC1

/-! # Sectional calculus of the frozen class off the axis

Integral equations on every anchored subinterval give AC sections and identify
their ordinary derivatives almost everywhere. The null endpoints are discarded.
-/

public section

open Set Filter MeasureTheory Topology

namespace EmcsfAcExtension.Local

private theorem ac_ae_of_integralForm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f g : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (h : ∀ x ∈ Icc a b, IntegralForm f g a x) :
    AbsolutelyContinuousOnInterval f a b ∧
      ∀ᵐ x ∂volume.restrict (Icc a b), HasDerivAt f (g x) x := by
  refine ⟨absolutelyContinuousOnInterval_of_integralForm_on hab h, ?_⟩
  rw [← restrict_Ioo_eq_restrict_Icc]
  filter_upwards [ae_restrict_of_ae ((h b ⟨hab, le_rfl⟩).1.ae_hasDerivAt_integral),
    ae_restrict_mem measurableSet_Ioo] with x hx hmem
  have hx' : x ∈ uIcc a b := by
    simpa only [uIcc_of_le hab] using (show x ∈ Icc a b from ⟨hmem.1.le, hmem.2.le⟩)
  have hp := (hx hx' a left_mem_uIcc).const_add (f a)
  apply hp.congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds hmem.1 hmem.2] with y hy
  exact (h y hy).eq_add_integral

variable {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}

/-- All seven outgoing equations give AC and their specified a.e. derivatives on
every off-axis closed outgoing segment. -/
theorem IsSolution.out_section (hS : IsSolution e S D) {u a b : ℝ}
    (hua : u < a) (hab : a ≤ b) (hseg : outSeg u a b ⊆ D) :
    (AbsolutelyContinuousOnInterval (S.r u) a b ∧
      ∀ᵐ v ∂volume.restrict (Icc a b), HasDerivAt (S.r u) (S.lam u v) v) ∧
    (AbsolutelyContinuousOnInterval (S.nu u) a b ∧
      ∀ᵐ v ∂volume.restrict (Icc a b), HasDerivAt (S.nu u) (S.rUV u v) v) ∧
    (AbsolutelyContinuousOnInterval (S.m u) a b ∧
      ∀ᵐ v ∂volume.restrict (Icc a b), HasDerivAt (S.m u) (S.mV u v) v) ∧
    (AbsolutelyContinuousOnInterval (S.Q u) a b ∧
      ∀ᵐ v ∂volume.restrict (Icc a b), HasDerivAt (S.Q u) (S.QV e u v) v) ∧
    (AbsolutelyContinuousOnInterval (S.A u) a b ∧
      ∀ᵐ v ∂volume.restrict (Icc a b), HasDerivAt (S.A u) (S.AV u v) v) ∧
    (AbsolutelyContinuousOnInterval (S.phi u) a b ∧
      ∀ᵐ v ∂volume.restrict (Icc a b), HasDerivAt (S.phi u) (S.phiV u v) v) ∧
    (AbsolutelyContinuousOnInterval (S.xi u) a b ∧
      ∀ᵐ v ∂volume.restrict (Icc a b), HasDerivAt (S.xi u) (S.xiV e u v) v) := by
  have h x (hx : x ∈ Icc a b) := hS.eq_out u a x hua hx.1
    (fun p hp => hseg ⟨hp.1, hp.2.1, hp.2.2.trans hx.2⟩)
  exact ⟨ac_ae_of_integralForm hab (fun x hx => (h x hx).1),
    ac_ae_of_integralForm hab (fun x hx => (h x hx).2.1),
    ac_ae_of_integralForm hab (fun x hx => (h x hx).2.2.1),
    ac_ae_of_integralForm hab (fun x hx => (h x hx).2.2.2.1),
    ac_ae_of_integralForm hab (fun x hx => (h x hx).2.2.2.2.1),
    ac_ae_of_integralForm hab (fun x hx => (h x hx).2.2.2.2.2.1),
    ac_ae_of_integralForm hab (fun x hx => (h x hx).2.2.2.2.2.2)⟩

/-- All six incoming equations give AC and their specified a.e. derivatives on
every off-axis closed incoming segment. -/
theorem IsSolution.in_section (hS : IsSolution e S D) {a b v : ℝ}
    (hab : a ≤ b) (hbv : b < v) (hseg : inSeg a b v ⊆ D) :
    (AbsolutelyContinuousOnInterval (fun u => S.r u v) a b ∧
      ∀ᵐ u ∂volume.restrict (Icc a b), HasDerivAt (fun x => S.r x v) (S.nu u v) u) ∧
    (AbsolutelyContinuousOnInterval (fun u => S.lam u v) a b ∧
      ∀ᵐ u ∂volume.restrict (Icc a b), HasDerivAt (fun x => S.lam x v) (S.rUV u v) u) ∧
    (AbsolutelyContinuousOnInterval (fun u => S.m u v) a b ∧
      ∀ᵐ u ∂volume.restrict (Icc a b), HasDerivAt (fun x => S.m x v) (S.mU u v) u) ∧
    (AbsolutelyContinuousOnInterval (fun u => S.Q u v) a b ∧
      ∀ᵐ u ∂volume.restrict (Icc a b), HasDerivAt (fun x => S.Q x v) (S.QU e u v) u) ∧
    (AbsolutelyContinuousOnInterval (fun u => S.phi u v) a b ∧
      ∀ᵐ u ∂volume.restrict (Icc a b), HasDerivAt (fun x => S.phi x v) (S.phiU e u v) u) ∧
    (AbsolutelyContinuousOnInterval (fun u => S.theta u v) a b ∧
      ∀ᵐ u ∂volume.restrict (Icc a b), HasDerivAt (fun x => S.theta x v) (S.thetaU e u v) u) := by
  have h x (hx : x ∈ Icc a b) := hS.eq_in a x v hx.1 (hx.2.trans_lt hbv)
    (fun p hp => hseg ⟨hp.1, hp.2.1.trans hx.2, hp.2.2⟩)
  exact ⟨ac_ae_of_integralForm hab (fun x hx => (h x hx).1),
    ac_ae_of_integralForm hab (fun x hx => (h x hx).2.1),
    ac_ae_of_integralForm hab (fun x hx => (h x hx).2.2.1),
    ac_ae_of_integralForm hab (fun x hx => (h x hx).2.2.2.1),
    ac_ae_of_integralForm hab (fun x hx => (h x hx).2.2.2.2.1),
    ac_ae_of_integralForm hab (fun x hx => (h x hx).2.2.2.2.2)⟩

private theorem section_derivative_of_integralForm {f g : ℝ → ℝ} {a b x : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hform : ∀ c ∈ Ioo a b, ∀ d ∈ Ioo a b, c ≤ d → IntegralForm f g c d)
    (hx : x ∈ Icc a b) : HasDerivWithinAt f (g x) (Icc a b) x := by
  by_cases hab' : a < b
  · let G (y : ℝ) := g (min (max a y) b)
    have cG : Continuous G := hg.comp_continuous
      ((continuous_const.max continuous_id).min continuous_const)
      (fun y => ⟨le_min (le_max_left _ _) hab, min_le_right _ _⟩)
    have fixG (y : ℝ) (hy : y ∈ Icc a b) : G y = g y := by
      dsimp [G]
      rw [max_eq_right hy.1, min_eq_left hy.2]
    have dG (y : ℝ) : HasDerivAt (fun y => ∫ s in a..y, G s) (G y) y :=
      intervalIntegral.integral_hasDerivAt_right (cG.intervalIntegrable a y)
        cG.stronglyMeasurable.stronglyMeasurableAtFilter cG.continuousAt
    have cprim : Continuous (fun y => ∫ s in a..y, G s) :=
      continuous_iff_continuousAt.mpr (fun y => (dG y).continuousAt)
    let P (y : ℝ) := f y - ∫ s in a..y, G s
    have cP : ContinuousOn P (Icc a b) := hf.sub cprim.continuousOn
    have hpair {c d : ℝ} (hc : c ∈ Ioo a b) (hd : d ∈ Ioo a b) (hcd : c ≤ d) :
        P c = P d := by
      have hi : f d - f c = ∫ s in c..d, G s := by
        rw [(hform c hc d hd hcd).2]
        apply intervalIntegral.integral_congr
        intro y hy
        rw [uIcc_of_le hcd] at hy
        exact (fixG y ⟨hc.1.le.trans hy.1, hy.2.trans hd.2.le⟩).symm
      have hp := intervalIntegral.integral_interval_sub_left
        (cG.intervalIntegrable (μ := volume) a d) (cG.intervalIntegrable (μ := volume) a c)
      dsimp [P]
      linarith
    have hmid : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
    have heq : EqOn P (fun _ => P ((a + b) / 2)) (Ioo a b) := by
      intro y hy
      rcases le_total y ((a + b) / 2) with h | h
      · exact hpair hy hmid h
      · exact (hpair hmid hy h).symm
    have heq' := heq.of_subset_closure cP continuousOn_const Ioo_subset_Icc_self
      (show Icc a b ⊆ closure (Ioo a b) by rw [closure_Ioo hab'.ne])
    have ha := heq' ⟨le_rfl, hab⟩
    have hrepr (y : ℝ) (hy : y ∈ Icc a b) : f y = f a + ∫ s in a..y, G s := by
      have hy' := heq' hy
      dsimp [P] at ha hy'
      rw [intervalIntegral.integral_same, sub_zero] at ha
      linarith
    have hder := (dG x).const_add (f a)
    rw [fixG x hx] at hder
    exact hder.hasDerivWithinAt.congr_of_mem hrepr hx
  · have heq : a = b := le_antisymm hab (le_of_not_gt hab')
    subst b
    exact HasFDerivWithinAt.of_subsingleton (by rw [Icc_self]; exact subsingleton_singleton)

/-- The frozen radius has continuous partials `ν, λ` on the closed triangle and
therefore is C¹ there, including the axis and both corners (internal project record). -/
theorem IsSolution.contDiffOn_r {a b : ℝ} (hS : IsSolution e S (triangle a b)) (hab : a < b) :
    ContDiffOn ℝ 1 (Function.uncurry S.r) (triangle a b) := by
  apply contDiffOn_uncurry_triangle_of_sectional_derivatives hab
    (U := S.nu) (V := S.lam) ?_ ?_ hS.cont_nu hS.cont_lam
  · intro u v hp
    have hs : MapsTo (fun x => (x, v)) (Icc a v) (triangle a b) :=
      fun x hx => ⟨hx.1, hx.2, hp.2.2⟩
    apply section_derivative_of_integralForm (hp.1.trans hp.2.1)
      (hS.cont_r.comp (continuous_id.prodMk continuous_const).continuousOn hs)
      (hS.cont_nu.comp (continuous_id.prodMk continuous_const).continuousOn hs) ?_
      ⟨hp.1, hp.2.1⟩
    intro c hc d hd hcd
    exact (hS.eq_in c d v hcd hd.2 (by
      rintro ⟨x, y⟩ ⟨hcx, hxd, rfl⟩
      exact ⟨hc.1.le.trans hcx, hxd.trans hd.2.le, hp.2.2⟩)).1
  · intro u v hp
    have hs : MapsTo (fun x => (u, x)) (Icc u b) (triangle a b) :=
      fun x hx => ⟨hp.1, hx.1, hx.2⟩
    apply section_derivative_of_integralForm (hp.2.1.trans hp.2.2)
      (hS.cont_r.comp (continuous_const.prodMk continuous_id).continuousOn hs)
      (hS.cont_lam.comp (continuous_const.prodMk continuous_id).continuousOn hs) ?_
      ⟨hp.2.1, hp.2.2⟩
    intro c hc d hd hcd
    exact (hS.eq_out u c d hc.1 hcd (by
      rintro ⟨x, y⟩ ⟨rfl, hcy, hyd⟩
      exact ⟨hp.1, hc.1.le.trans hcy, hyd.trans hd.2.le⟩)).1

end EmcsfAcExtension.Local
