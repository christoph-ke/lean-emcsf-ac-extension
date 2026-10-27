module

public import EmcsfAcExtension.Frozen.OrigDomain
public import EmcsfAcExtension.Local.Calculus.Sections

/-! # Reality of the scalar transport fields on the original domain

internal project record R2: real `phi` determines real `theta` and `xi` through non-degenerate
characteristic sections. Continuity includes the axis and the initial corner.
-/

public section

open Set MeasureTheory Filter Topology Complex

namespace EmcsfAcExtension.Global.Real

/-- [internal] Continuity restricts to an outgoing characteristic section. -/
private theorem continuous_out {E : Type*} [TopologicalSpace E]
    {f : ℝ → ℝ → E} {D : Set (ℝ × ℝ)} {u a b : ℝ}
    (hf : ContinuousOn (Function.uncurry f) D) (hs : outSeg u a b ⊆ D) :
    ContinuousOn (f u) (Icc a b) :=
  hf.comp (f := fun v => (u, v)) (continuous_const.prodMk continuous_id).continuousOn
    (fun _ hx => hs ⟨rfl, hx⟩)

/-- [internal] Continuity restricts to an incoming characteristic section. -/
private theorem continuous_in {E : Type*} [TopologicalSpace E]
    {f : ℝ → ℝ → E} {D : Set (ℝ × ℝ)} {a b v : ℝ}
    (hf : ContinuousOn (Function.uncurry f) D) (hs : inSeg a b v ⊆ D) :
    ContinuousOn (fun u => f u v) (Icc a b) :=
  hf.comp (f := fun u => (u, v)) (continuous_id.prodMk continuous_const).continuousOn
    (fun _ hx => hs ⟨hx.1, hx.2, rfl⟩)

/-- [internal] A continuous density of a real primitive is real, including endpoints
of every non-degenerate section. -/
private theorem density_im_zero {f g : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hg : ContinuousOn (fun x => (g x).im) (Icc a b))
    (hr : ∀ x ∈ Icc a b, (f x).im = 0)
    (hd : ∀ᵐ x ∂volume.restrict (Icc a b), HasDerivAt f (g x) x) :
    ∀ x ∈ Icc a b, (g x).im = 0 := by
  have he : (fun x => (g x).im) =ᵐ[volume.restrict (Icc a b)] (fun _ => 0) := by
    filter_upwards [hd, ae_restrict_mem measurableSet_Icc] with x hx hmem
    have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hx
    have hz : HasDerivWithinAt (fun _ : ℝ => (0 : ℝ)) (g x).im (Icc a b) x :=
      hi.hasDerivWithinAt.congr_of_mem (fun y hy => (hr y hy).symm) hmem
    simpa using (hz.derivWithin (uniqueDiffOn_Icc hab x hmem)).symm
  exact MeasureTheory.Measure.eqOn_Icc_of_ae_eq volume hab.ne he hg continuousOn_const

/-- [internal] Outgoing sections determine the reality of `theta` off the axis. -/
private theorem theta_im_zero_offAxis {ui : ℝ} {S : Fields}
    (hS : IsSolution 0 S (origDomain ui))
    (hr : ∀ p ∈ origDomain ui, (S.phi p.1 p.2).im = 0)
    {u v : ℝ} (hp : (u, v) ∈ origDomain ui) (huv : u < v) :
    (S.theta u v).im = 0 := by
  let a := (u + v) / 2
  have hua : u < a := by dsimp [a]; linarith
  have hav : a < v := by dsimp [a]; linarith
  have hs : outSeg u a v ⊆ origDomain ui := by
    rintro ⟨x, y⟩ ⟨rfl, hay, hyv⟩
    exact ⟨hp.1, hp.2.1, hua.le.trans hay, hyv.trans hp.2.2.2⟩
  have hden : ∀ x ∈ Icc a v, S.r u x ≠ 0 := fun x hx =>
    (hS.r_pos (u, x) (hs ⟨rfl, hx⟩) (hua.trans_le hx.1)).ne'
  have hg : ContinuousOn (fun x => (S.phiV u x).im) (Icc a v) := by
    simp only [Fields.phiV, Complex.div_ofReal_im]
    exact (Complex.continuous_im.comp_continuousOn (f := S.theta u)
      (continuous_out hS.cont_theta hs)).div (continuous_out hS.cont_r hs) hden
  have hd := (EmcsfAcExtension.Local.IsSolution.out_section hS hua hav.le hs).2.2.2.2.2.1.2
  have hz := density_im_zero hav hg (fun x hx => hr (u, x) (hs ⟨rfl, hx⟩)) hd
    v ⟨hav.le, le_rfl⟩
  simpa only [Fields.phiV, Complex.div_ofReal_im, div_eq_zero_iff,
    hden v ⟨hav.le, le_rfl⟩, or_false] using hz

/-- [internal] Incoming sections determine the reality of `xi` off the axis. -/
private theorem xi_im_zero_offAxis {ui : ℝ} {S : Fields}
    (hS : IsSolution 0 S (origDomain ui))
    (hr : ∀ p ∈ origDomain ui, (S.phi p.1 p.2).im = 0)
    {u v : ℝ} (hp : (u, v) ∈ origDomain ui) (huv : u < v) :
    (S.xi u v).im = 0 := by
  let b := (u + v) / 2
  have hub : u < b := by dsimp [b]; linarith
  have hbv : b < v := by dsimp [b]; linarith
  have hs : inSeg u b v ⊆ origDomain ui := by
    rintro ⟨x, y⟩ ⟨hux, hxb, rfl⟩
    exact ⟨hp.1.trans hux, (hxb.trans_lt hbv).trans_le hp.2.2.2,
      hxb.trans hbv.le, hp.2.2.2⟩
  have hden : ∀ x ∈ Icc u b, S.r x v ≠ 0 := fun x hx =>
    (hS.r_pos (x, v) (hs ⟨hx.1, hx.2, rfl⟩) (hx.2.trans_lt hbv)).ne'
  have hg : ContinuousOn (fun x => (S.phiU 0 x v).im) (Icc u b) := by
    simp only [Fields.phiU, Complex.ofReal_zero, mul_zero, zero_mul, sub_zero,
      Complex.div_ofReal_im]
    exact (Complex.continuous_im.comp_continuousOn (f := fun x => S.xi x v)
      (continuous_in hS.cont_xi hs)).div (continuous_in hS.cont_r hs) hden
  have hd := (EmcsfAcExtension.Local.IsSolution.in_section hS hub.le hbv hs).2.2.2.2.1.2
  have hz := density_im_zero hub hg (fun x hx => hr (x, v) (hs ⟨hx.1, hx.2, rfl⟩)) hd
    u ⟨le_rfl, hub.le⟩
  simpa only [Fields.phiU, Complex.ofReal_zero, mul_zero, zero_mul, sub_zero,
    Complex.div_ofReal_im, div_eq_zero_iff, hden u ⟨le_rfl, hub.le⟩, or_false] using hz

/-- [internal] Off-axis reality extends to every old axis point along an outgoing
section; this also covers the initial corner `t = ui`. -/
private theorem im_zero_axis {ui t : ℝ} {f : ℝ → ℝ → ℂ}
    (hc : ContinuousOn (Function.uncurry f) (origDomain ui))
    (hz : ∀ u v, (u, v) ∈ origDomain ui → u < v → (f u v).im = 0)
    (ht : (t, t) ∈ origDomain ui) : (f t t).im = 0 := by
  have hs : outSeg t t 0 ⊆ origDomain ui := by
    rintro ⟨x, y⟩ ⟨rfl, hty, hy0⟩
    exact ⟨ht.1, ht.2.1, hty, hy0⟩
  have c : ContinuousOn (fun v => (f t v).im) (Icc t 0) :=
    Complex.continuous_im.comp_continuousOn (f := f t) (continuous_out hc hs)
  have he : EqOn (fun v => (f t v).im) (fun _ => 0) (Ioo t 0) :=
    fun v hv => hz t v (hs ⟨rfl, hv.1.le, hv.2.le⟩) hv.1
  have he' := he.of_subset_closure c continuousOn_const Ioo_subset_Icc_self
    (show Icc t 0 ⊆ closure (Ioo t 0) by rw [closure_Ioo ht.2.1.ne])
  exact he' ⟨le_rfl, ht.2.1.le⟩

/-- On the original domain, real `phi` forces both scalar transport fields to be
real, with no additional hypotheses (internal project record R2). -/
theorem theta_xi_im_zero_of_phi_im_zero {ui : ℝ} {S : Fields}
    (hS : IsSolution 0 S (origDomain ui))
    (hreal : ∀ p ∈ origDomain ui, (S.phi p.1 p.2).im = 0) :
    ∀ p ∈ origDomain ui, (S.theta p.1 p.2).im = 0 ∧ (S.xi p.1 p.2).im = 0 := by
  rintro ⟨u, v⟩ hp
  rcases hp.2.2.1.eq_or_lt with heq | hlt
  · change u = v at heq
    subst v
    exact ⟨im_zero_axis hS.cont_theta (fun _ _ => theta_im_zero_offAxis hS hreal) hp,
      im_zero_axis hS.cont_xi (fun _ _ => xi_im_zero_offAxis hS hreal) hp⟩
  · exact ⟨theta_im_zero_offAxis hS hreal hp hlt, xi_im_zero_offAxis hS hreal hp hlt⟩

end EmcsfAcExtension.Global.Real
