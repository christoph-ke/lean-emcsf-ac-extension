module

public import EmcsfAcExtension.Local.Broad.GeometryContinuity
public import EmcsfAcExtension.Local.Broad.GeometryODE
import EmcsfAcExtension.Local.Algebra.Raychaudhuri

/-! # Optical identities directly in the broad integral class

The characteristic sources are continuous off the axis. Their integral
equations therefore give ordinary interior derivatives. Endpoint optical
identities use continuous logarithms and the matching integrable flux;
no C¹ hypothesis on either competing solution is introduced.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Local.Broad

/-- The incoming optical logarithm is continuous on a complete section,
including its axis endpoint. This uses the frozen axis mass-ratio limit. -/
theorem continuousOn_log_kappa_in {e u v : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) (hs : inSeg u v v ⊆ D) :
    ContinuousOn (fun x => Real.log (S.lam x v / (1 - S.mu x v))) (Icc u v) := by
  have cl := continuousOn_in_section hS.cont_lam hs
  have cm := continuousOn_in_section (continuousOn_mu hS) hs
  have cg : ContinuousOn (fun x => 1 - S.mu x v) (Icc u v) := continuousOn_const.sub cm
  exact (cl.div cg (fun x hx => (hS.one_sub_mu_pos (x, v) (hs ⟨hx.1, hx.2, rfl⟩)).ne')).log
    (fun x hx => div_ne_zero (hS.lam_pos (x, v) (hs ⟨hx.1, hx.2, rfl⟩)).ne'
      (hS.one_sub_mu_pos (x, v) (hs ⟨hx.1, hx.2, rfl⟩)).ne')

/-- The outgoing optical logarithm is continuous on a complete section,
with its actual coupled axis expansion. There are no smallness premises. -/
theorem continuousOn_log_iota_out {e u v : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) (hs : outSeg u u v ⊆ D) :
    ContinuousOn (fun x => Real.log (-S.nu u x / (1 - S.mu u x))) (Icc u v) := by
  have cn := (continuousOn_out_section hS.cont_nu hs).neg
  have cm := continuousOn_out_section (continuousOn_mu hS) hs
  have cg : ContinuousOn (fun x => 1 - S.mu u x) (Icc u v) := continuousOn_const.sub cm
  exact (cn.div cg (fun x hx => (hS.one_sub_mu_pos (u, x) (hs ⟨rfl, hx⟩)).ne')).log
    (fun x hx => div_ne_zero (neg_ne_zero.mpr (hS.nu_neg (u, x) (hs ⟨rfl, hx⟩)).ne)
      (hS.one_sub_mu_pos (u, x) (hs ⟨rfl, hx⟩)).ne')

/-- The outgoing expansion has its incoming ordinary derivative in the open
part of a complete incoming section of a frozen solution. -/
theorem hasDerivAt_lam_in {e u v x : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) (hs : inSeg u v v ⊆ D) (hx : x ∈ Ioo u v) :
    HasDerivAt (fun y => S.lam y v) (S.rUV x v) x := by
  have sect {f : ℝ → ℝ → ℝ} (hf : ContinuousOn (Function.uncurry f) D) :=
    (continuousOn_in_section hf hs).mono Ioo_subset_Icc_self
  have cr := sect hS.cont_r
  have cm := sect hS.cont_m
  have cl := sect hS.cont_lam
  have cn := sect hS.cont_nu
  have cq := sect hS.cont_Q
  have nr : ∀ y ∈ Ioo u v, S.r y v ≠ 0 := fun y hy =>
    (hS.r_pos (y, v) (hs ⟨hy.1.le, hy.2.le, rfl⟩) hy.2).ne'
  have cμ : ContinuousOn (fun y => S.mu y v) (Ioo u v) := (continuousOn_const.mul cm).div cr nr
  have cg : ContinuousOn (fun y => 1 - S.mu y v) (Ioo u v) := continuousOn_const.sub cμ
  have ng : ∀ y ∈ Ioo u v, 1 - S.mu y v ≠ 0 := fun y hy =>
    (hS.one_sub_mu_pos (y, v) (hs ⟨hy.1.le, hy.2.le, rfl⟩)).ne'
  have csource : ContinuousOn (fun y => S.rUV y v) (Ioo u v) :=
    ((cn.mul cl).div cr nr).mul
      ((cμ.sub ((cq.pow 2).div (cr.pow 2) (fun y hy => pow_ne_zero 2 (nr y hy)))).div cg ng)
  apply hasDerivAt_of_integralForm_interior hx csource
  intro c d hc hcd hd
  exact (hS.eq_in c d v hcd hd (by
    rintro p ⟨hp₁, hp₂, rfl⟩
    exact hs ⟨hc.le.trans hp₁, hp₂.trans hd.le, rfl⟩)).2.1

/-- The incoming logarithmic Raychaudhuri equation in the broad class, with
its exact normalized quadratic flux and sign. -/
theorem hasDerivAt_log_kappa_in {e u v x : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) (hs : inSeg u v v ⊆ D) (hx : x ∈ Ioo u v) :
    HasDerivAt (fun y => Real.log (S.lam y v / (1 - S.mu y v)))
      (-((-S.nu x v) / S.r x v * ‖S.xi x v / S.nu x v‖ ^ 2)) x := by
  have hp : (x, v) ∈ D := hs ⟨hx.1.le, hx.2.le, rfl⟩
  have hr := (hS.r_pos (x, v) hp hx.2).ne'
  have hl := (hS.lam_pos (x, v) hp).ne'
  have hn := (hS.nu_neg (x, v) hp).ne
  have hg := (hS.one_sub_mu_pos (x, v) hp).ne'
  have dμ : HasDerivAt (fun y => S.mu y v)
      (2 * S.mU x v / S.r x v - 2 * S.m x v * S.nu x v / S.r x v ^ 2) x := by
    apply (((IsSolution.hasDerivAt_mass_in hS hs hx).const_mul 2).div
      (hasDerivAt_radius_in hS hs hx) hr).congr_deriv
    field_simp [hr]
  have hd := ((hasDerivAt_lam_in hS hs hx).div (dμ.const_sub 1) hg).log (div_ne_zero hl hg)
  apply hd.congr_deriv
  calc
    _ = S.rUV x v / S.lam x v +
        (2 * S.mU x v / S.r x v - 2 * S.m x v * S.nu x v / S.r x v ^ 2) /
          (1 - S.mu x v) := by
            simp only [Pi.div_apply]
            field_simp [hl, hg]
            ring
    _ = ‖S.xi x v‖ ^ 2 / (S.nu x v * S.r x v) :=
      eq_ray_in_algebra hr hl hn hg rfl rfl
    _ = _ := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, div_pow, sq_abs]
      field_simp [hr, hn]

/-- The outgoing logarithmic Raychaudhuri equation in the broad class, with
the exact positive normalized scalar flux. -/
theorem hasDerivAt_log_iota_out {e u v x : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) (hs : outSeg u u v ⊆ D) (hx : x ∈ Ioo u v) :
    HasDerivAt (fun y => Real.log (-S.nu u y / (1 - S.mu u y)))
      (S.lam u x / S.r u x * ‖S.theta u x / S.lam u x‖ ^ 2) x := by
  have hp : (u, x) ∈ D := hs ⟨rfl, hx.1.le, hx.2.le⟩
  have hr := (hS.r_pos (u, x) hp hx.1).ne'
  have hl := (hS.lam_pos (u, x) hp).ne'
  have hn := (hS.nu_neg (u, x) hp).ne
  have hg := (hS.one_sub_mu_pos (u, x) hp).ne'
  have dμ : HasDerivAt (S.mu u)
      (2 * S.mV u x / S.r u x - 2 * S.m u x * S.lam u x / S.r u x ^ 2) x := by
    apply (((IsSolution.hasDerivAt_mass_out hS hs hx).const_mul 2).div
      (IsSolution.hasDerivAt_radius_out hS hs hx) hr).congr_deriv
    field_simp [hr]
  have hd := ((hasDerivAt_nu_out hS hs hx).neg.div
    (dμ.const_sub 1) hg).log (div_ne_zero (neg_ne_zero.mpr hn) hg)
  apply hd.congr_deriv
  calc
    _ = S.rUV u x / S.nu u x +
        (2 * S.mV u x / S.r u x - 2 * S.m u x * S.lam u x / S.r u x ^ 2) /
          (1 - S.mu u x) := by
            simp only [Pi.div_apply, Pi.neg_apply]
            field_simp [hn, hg]
            ring
    _ = ‖S.theta u x‖ ^ 2 / (S.lam u x * S.r u x) :=
      eq_ray_out_algebra hr hl hn hg rfl rfl
    _ = _ := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, div_pow, sq_abs]
      field_simp [hr, hl]

end EmcsfAcExtension.Local.Broad
