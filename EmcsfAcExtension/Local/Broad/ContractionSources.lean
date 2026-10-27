module

public import EmcsfAcExtension.Local.Broad.GeometryRay
import EmcsfAcExtension.Local.Algebra.Normalized

/-! # Normalized scalar transports in the frozen broad class

Only the characteristic integral equations and off-axis continuity are
used. Incoming differentiability of the normalized incoming field is
neither asserted nor needed.
-/

public section

open Set Complex

namespace EmcsfAcExtension.Local.Broad

/-- The charged wave forcing is continuous away from the regular axis in
the broad class. The assertion is qualitative and has no constants. -/
theorem continuousOn_waveSource_off_axis {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) :
    ContinuousOn (Function.uncurry (S.waveSource e)) (D ∩ {p | p.1 < p.2}) := by
  have hsub : D ∩ {p | p.1 < p.2} ⊆ D := inter_subset_left
  have cr := continuous_ofReal.comp_continuousOn (hS.cont_r.mono hsub)
  have cl := continuous_ofReal.comp_continuousOn (hS.cont_lam.mono hsub)
  have cn := continuous_ofReal.comp_continuousOn (hS.cont_nu.mono hsub)
  have cq := continuous_ofReal.comp_continuousOn (hS.cont_Q.mono hsub)
  have cp := hS.cont_phi.mono hsub
  have cm := continuous_ofReal.comp_continuousOn ((continuousOn_mu hS).mono hsub)
  apply (((((continuousOn_const.mul continuousOn_const).mul cq).mul cp).mul cn).mul cl).div
    ((continuousOn_const.sub cm).mul cr)
  intro p hp
  apply mul_ne_zero
  · change 1 - (S.mu p.1 p.2 : ℂ) ≠ 0
    exact_mod_cast (hS.one_sub_mu_pos p hp.1).ne'
  · change (S.r p.1 p.2 : ℂ) ≠ 0
    exact_mod_cast (hS.r_pos p hp.1 hp.2).ne'

/-- The outgoing source of the incoming scalar transport field is
continuous away from the axis. No ordinary incoming derivative is used. -/
theorem continuousOn_xiV_off_axis {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) :
    ContinuousOn (Function.uncurry (S.xiV e)) (D ∩ {p | p.1 < p.2}) := by
  have hsub : D ∩ {p | p.1 < p.2} ⊆ D := inter_subset_left
  have cn := continuous_ofReal.comp_continuousOn (hS.cont_nu.mono hsub)
  have cr := continuous_ofReal.comp_continuousOn (hS.cont_r.mono hsub)
  have ct := hS.cont_theta.mono hsub
  exact (((cn.mul ct).div cr (fun p hp => by
    change (S.r p.1 p.2 : ℂ) ≠ 0
    exact_mod_cast (hS.r_pos p hp.1 hp.2).ne')).neg).add
    (continuousOn_waveSource_off_axis hS)

/-- Restriction of the incoming scalar integral equation to its actual source.
The endpoints are off the axis; no regularity upgrade is assumed. -/
theorem theta_in_integralForm {e a b v : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) (hab : a ≤ b) (hbv : b < v) (hs : inSeg a b v ⊆ D) :
    IntegralForm (fun y => S.theta y v) (fun y => S.thetaU e y v) a b :=
  (hS.eq_in a b v hab hbv hs).2.2.2.2.2

/-- Off-axis incoming continuity of the outgoing scalar source, with the
section map fixed explicitly. -/
theorem continuousOn_thetaU_in {e u v : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) (hs : inSeg u v v ⊆ D) :
    ContinuousOn (fun y => S.thetaU e y v) (Ioo u v) := by
  have hsub : Ioo u v ⊆ Icc u v := Ioo_subset_Icc_self
  have cr := continuous_ofReal.comp_continuousOn ((continuousOn_in_section hS.cont_r hs).mono hsub)
  have cl := continuous_ofReal.comp_continuousOn
    ((continuousOn_in_section hS.cont_lam hs).mono hsub)
  have cn := continuous_ofReal.comp_continuousOn ((continuousOn_in_section hS.cont_nu hs).mono hsub)
  have cq := continuous_ofReal.comp_continuousOn ((continuousOn_in_section hS.cont_Q hs).mono hsub)
  have ca := continuous_ofReal.comp_continuousOn ((continuousOn_in_section hS.cont_A hs).mono hsub)
  have cm := continuous_ofReal.comp_continuousOn
    ((continuousOn_in_section (continuousOn_mu hS) hs).mono hsub)
  have cp := (continuousOn_in_section hS.cont_phi hs).mono hsub
  have ct := (continuousOn_in_section hS.cont_theta hs).mono hsub
  have cx := (continuousOn_in_section hS.cont_xi hs).mono hsub
  have hr x (hx : x ∈ Ioo u v) : (S.r x v : ℂ) ≠ 0 := by
    exact_mod_cast (hS.r_pos (x, v) (hs ⟨hx.1.le, hx.2.le, rfl⟩) hx.2).ne'
  have hg x (hx : x ∈ Ioo u v) : 1 - (S.mu x v : ℂ) ≠ 0 := by
    exact_mod_cast (hS.one_sub_mu_pos (x, v) (hs ⟨hx.1.le, hx.2.le, rfl⟩)).ne'
  change ContinuousOn (fun x => -(I * e * S.A x v * S.theta x v) -
    S.lam x v * S.xi x v / S.r x v - S.waveSource e x v) (Ioo u v)
  exact ((((continuousOn_const.mul continuousOn_const).mul ca).mul ct).neg.sub
    ((cl.mul cx).div cr hr)).sub
      ((((((continuousOn_const.mul continuousOn_const).mul cq).mul cp).mul cn).mul cl).div
        ((continuousOn_const.sub cm).mul cr) (fun x hx => mul_ne_zero (hg x hx) (hr x hx)))

/-- The outgoing scalar transport field has its prescribed incoming
ordinary derivative at every interior point of a complete incoming section. -/
theorem hasDerivAt_theta_in {e u v x : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) (hs : inSeg u v v ⊆ D) (hx : x ∈ Ioo u v) :
    HasDerivAt (fun y => S.theta y v) (S.thetaU e x v) x := by
  refine hasDerivAt_of_integralForm_interior hx (continuousOn_thetaU_in hS hs) ?_
  intro a b ha hab hb
  exact theta_in_integralForm hS hab hb (by
    rintro ⟨c, d⟩ ⟨hc, hd, rfl⟩
    exact hs ⟨ha.le.trans hc, hd.trans hb.le, rfl⟩)

/-- The incoming scalar transport field has its ordinary outgoing
derivative throughout the interior of a complete outgoing section. -/
theorem hasDerivAt_xi_out {e u v x : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) (hs : outSeg u u v ⊆ D) (hx : x ∈ Ioo u v) :
    HasDerivAt (S.xi u) (S.xiV e u x) x := by
  have hpmap : MapsTo (fun y : ℝ => (u, y)) (Ioo u v) (D ∩ {p | p.1 < p.2}) :=
    fun y hy => ⟨hs ⟨rfl, hy.1.le, hy.2.le⟩, hy.1⟩
  have cc : ContinuousOn (S.xiV e u) (Ioo u v) :=
    (continuousOn_xiV_off_axis hS).comp (f := fun y : ℝ => (u, y))
      (continuous_const.prodMk continuous_id).continuousOn
      hpmap
  apply hasDerivAt_of_integralForm_interior hx cc
  intro a b ha hab hb
  exact (hS.eq_out u a b ha hab (by
    rintro ⟨c, d⟩ ⟨rfl, hd⟩
    exact hs ⟨rfl, ha.le.trans hd.1, hd.2.trans hb.le⟩)).2.2.2.2.2.2

/-- The ordinary incoming normalized `a` equation, directly for broad
solutions. The real connection term has the literal frozen sign. -/
theorem hasDerivAt_a_in {e u v x : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) (hs : inSeg u v v ⊆ D) (hx : x ∈ Ioo u v) :
    HasDerivAt (fun y => S.a y v)
      (-(I * e * S.A x v * S.a x v) + (-(S.nu x v : ℂ) / S.r x v) *
        (((S.mu x v : ℂ) - S.Q x v ^ 2 / (S.r x v : ℂ) ^ 2) /
          (1 - S.mu x v) * (S.theta x v / S.lam x v) +
          I * e * S.Q x v * S.phi x v / (1 - S.mu x v))) x := by
  have hp : (x, v) ∈ D := hs ⟨hx.1.le, hx.2.le, rfl⟩
  have hlC : (S.lam x v : ℂ) ≠ 0 := by exact_mod_cast (hS.lam_pos (x, v) hp).ne'
  have hd := (hasDerivAt_phi_in hS hs hx).add
    ((hasDerivAt_theta_in hS hs hx).div (hasDerivAt_lam_in hS hs hx).ofReal_comp hlC)
  have ha := eq_normalized_in_algebra (r := S.r x v) (lam := S.lam x v) (nu := S.nu x v)
    (mu := S.mu x v) (Q := S.Q x v) (e := e) (A := S.A x v) (phi := S.phi x v)
    (theta := S.theta x v) (xi := S.xi x v) (lamU := S.rUV x v)
    (phiU := S.phiU e x v) (thetaU := S.thetaU e x v) (hS.r_pos (x, v) hp hx.2).ne'
    (hS.lam_pos (x, v) hp).ne' (hS.one_sub_mu_pos (x, v) hp).ne' rfl rfl rfl
  apply hd.congr_deriv
  rw [Fields.a]
  linear_combination ha

/-- The ordinary outgoing normalized `b` equation for broad solutions.
Its initial endpoint is the actual axis scalar, which equals `a` there. -/
theorem hasDerivAt_b_out {e u v x : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) (hs : outSeg u u v ⊆ D) (hx : x ∈ Ioo u v) :
    HasDerivAt (S.b u)
      ((-(S.lam u x : ℂ) / S.r u x) *
        (((S.mu u x : ℂ) - S.Q u x ^ 2 / (S.r u x : ℂ) ^ 2) /
          (1 - S.mu u x) * (S.xi u x / S.nu u x) -
          I * e * S.Q u x * S.phi u x / (1 - S.mu u x))) x := by
  have hp : (u, x) ∈ D := hs ⟨rfl, hx.1.le, hx.2.le⟩
  have hnC : (S.nu u x : ℂ) ≠ 0 := by exact_mod_cast (hS.nu_neg (u, x) hp).ne
  have hd := (hasDerivAt_phi_out hS hs hx).add
    ((hasDerivAt_xi_out hS hs hx).div (hasDerivAt_nu_out hS hs hx).ofReal_comp hnC)
  apply hd.congr_deriv
  exact eq_normalized_out_algebra (r := S.r u x) (lam := S.lam u x) (nu := S.nu u x)
    (mu := S.mu u x) (Q := S.Q u x) (e := e) (phi := S.phi u x) (theta := S.theta u x)
    (xi := S.xi u x) (hS.r_pos (u, x) hp hx.1).ne' (hS.nu_neg (u, x) hp).ne
    (hS.one_sub_mu_pos (u, x) hp).ne' rfl rfl rfl

/-- Incoming normalized transport with real mass and electric-square
coefficients, in the form used by the weighted scalar comparison. -/
theorem hasDerivAt_a_in_real_coefficients {e u v x : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) (hs : inSeg u v v ⊆ D) (hx : x ∈ Ioo u v) :
    HasDerivAt (fun y => S.a y v)
      ((((-S.nu x v) / S.r x v : ℝ) : ℂ) *
        (((S.mu x v - S.Q x v ^ 2 / S.r x v ^ 2) / (1 - S.mu x v) : ℝ) : ℂ) *
        (S.theta x v / S.lam x v) +
      I * e * (((-S.nu x v : ℝ) : ℂ) / S.r x v) * S.Q x v * S.phi x v /
        (1 - S.mu x v) - I * e * S.A x v * S.a x v) x := by
  apply (hasDerivAt_a_in hS hs hx).congr_deriv
  push_cast
  ring

/-- Outgoing normalized transport with real mass and electric-square
coefficients. No ordinary incoming derivative of `b` is asserted. -/
theorem hasDerivAt_b_out_real_coefficients {e u v x : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) (hs : outSeg u u v ⊆ D) (hx : x ∈ Ioo u v) :
    HasDerivAt (S.b u)
      (-(((S.lam u x / S.r u x : ℝ) : ℂ) *
        (((S.mu u x - S.Q u x ^ 2 / S.r u x ^ 2) / (1 - S.mu u x) : ℝ) : ℂ) *
        (S.xi u x / S.nu u x)) +
      I * e * ((S.lam u x : ℂ) / S.r u x) * S.Q u x * S.phi u x /
        (1 - S.mu u x)) x := by
  apply (hasDerivAt_b_out hS hs hx).congr_deriv
  push_cast
  ring

end EmcsfAcExtension.Local.Broad
