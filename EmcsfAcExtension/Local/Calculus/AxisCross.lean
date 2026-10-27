module

public import EmcsfAcExtension.Local.Calculus.AxisRatio
public import EmcsfAcExtension.Local.Calculus.Normalized
import EmcsfAcExtension.Infra.Calculus.PartialsC1

/-! # Vanishing cross transports at the regular center

The radius equation removes the singular coefficient multiplying the normalized scalar
ratio. The charge quotient and the continuous mass ratio supply the remaining axis limit.
-/

public section

open Set Complex

namespace EmcsfAcExtension.Local

/-- The incoming normalized transport rewritten using `∂ᵤλ/λ`. This form has a
continuous axis extension once `Q/r` is extended by zero. -/
theorem pdU_a_transport_aux {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    pdU (triangle 0 T) S.a u v = -(I * e * S.A u v * S.a u v) -
      (pdU (triangle 0 T) S.lam u v / S.lam u v : ℝ) *
        (S.theta u v / S.lam u v) -
      I * e * S.nu u v * (S.Q u v / S.r u v : ℝ) * S.phi u v / (1 - S.mu u v) := by
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have h := (uniqueDiffOn_Icc (hu.trans_lt huv) u ⟨hu, huv.le⟩).eq_deriv _
    (hasDerivWithinAt_u_aux (c1_a_aux hS) hu huv.le hvT)
    (eq_normalized_in hS hu huv hvT)
  rw [h, (hS.eq_u _ hp huv).2.1]
  dsimp only [Fields.rUV]
  have hr : (S.r u v : ℂ) ≠ 0 := by exact_mod_cast (hS.r_pos _ hp huv).ne'
  have hl : (S.lam u v : ℂ) ≠ 0 := by exact_mod_cast (hS.lam_pos _ hp).ne'
  have hm : 1 - (S.mu u v : ℂ) ≠ 0 := by
    exact_mod_cast (hS.one_sub_mu_pos _ hp).ne'
  push_cast
  field_simp [hr, hl, hm]
  ring

/-- The outgoing normalized transport rewritten using `∂ᵥν/ν`. Its axis limit
uses the same continuous charge quotient as the incoming equation. -/
theorem pdV_b_transport_aux {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    pdV (triangle 0 T) S.b u v =
      -(pdV (triangle 0 T) S.nu u v / S.nu u v : ℝ) * (S.xi u v / S.nu u v) +
      I * e * S.lam u v * (S.Q u v / S.r u v : ℝ) * S.phi u v / (1 - S.mu u v) := by
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have h := (uniqueDiffOn_Icc (huv.trans_le hvT) v ⟨huv.le, hvT⟩).eq_deriv _
    (hasDerivWithinAt_v_aux (c1_b_aux hS) hu huv.le hvT)
    (eq_normalized_out hS hu huv hvT)
  rw [h, (hS.eq_v _ hp huv).2.1]
  dsimp only [Fields.rUV]
  have hr : (S.r u v : ℂ) ≠ 0 := by exact_mod_cast (hS.r_pos _ hp huv).ne'
  have hn : (S.nu u v : ℂ) ≠ 0 := by exact_mod_cast (hS.nu_neg _ hp).ne
  have hm : 1 - (S.mu u v : ℂ) ≠ 0 := by
    exact_mod_cast (hS.one_sub_mu_pos _ hp).ne'
  push_cast
  field_simp [hr, hn, hm]
  ring

/-- Incoming covariant cross transport of `a` vanishes at the axis; the outgoing
cross derivative of `b` vanishes there. The scalar part is gauge covariant. -/
theorem scalar_axis_cross_partials_aux {e T : ℝ} {S : Fields} (hT : 0 < T)
    (hS : IsC1Solution e S (triangle 0 T)) {t : ℝ} (ht : t ∈ Icc 0 T) :
    pdU (triangle 0 T) S.a t t = -(I * e * S.A t t * S.phi t t) ∧
      pdV (triangle 0 T) S.b t t = 0 := by
  obtain ⟨q, cq, hq, hqaxis⟩ := exists_continuous_charge_ratio_aux hT hS
  have cm := continuousOn_mu_aux hT hS
  have cl := continuousOn_partial_u hS.c1_lam (uniqueDiffOn_triangle hT)
  have cn := continuousOn_partial_v hS.c1_nu (uniqueDiffOn_triangle hT)
  have cL : ContinuousOn (fun p : ℝ × ℝ => (S.lam p.1 p.2 : ℂ)) (triangle 0 T) :=
    continuous_ofReal.comp_continuousOn hS.c1_lam.continuousOn
  have cN : ContinuousOn (fun p : ℝ × ℝ => (S.nu p.1 p.2 : ℂ)) (triangle 0 T) :=
    continuous_ofReal.comp_continuousOn hS.c1_nu.continuousOn
  have cQ : ContinuousOn (fun p => (q p : ℂ)) (triangle 0 T) :=
    continuous_ofReal.comp_continuousOn cq
  have cH : ContinuousOn (fun p : ℝ × ℝ => 1 - (S.mu p.1 p.2 : ℂ))
      (triangle 0 T) := continuousOn_const.sub (continuous_ofReal.comp_continuousOn cm)
  have hln (p : ℝ × ℝ) (hp : p ∈ triangle 0 T) : (S.lam p.1 p.2 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (hS.lam_pos p hp).ne'
  have hnn (p : ℝ × ℝ) (hp : p ∈ triangle 0 T) : (S.nu p.1 p.2 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (hS.nu_neg p hp).ne
  have hhn (p : ℝ × ℝ) (hp : p ∈ triangle 0 T) :
      1 - (S.mu p.1 p.2 : ℂ) ≠ 0 := by
    exact_mod_cast (hS.one_sub_mu_pos p hp).ne'
  have ca := (((continuousOn_const (c := I * e)).mul
    (continuous_ofReal.comp_continuousOn hS.c1_A.continuousOn)).mul
      (c1_a_aux hS).continuousOn).neg
  have cx := hS.c1_theta.continuousOn.div cL hln
  have cy := hS.c1_xi.continuousOn.div cN hnn
  have cp := hS.c1_phi.continuousOn
  have cE := ((((continuousOn_const (c := I * e)).mul cN).mul cQ).mul cp).div cH hhn
  have cE' := ((((continuousOn_const (c := I * e)).mul cL).mul cQ).mul cp).div cH hhn
  have cR := continuous_ofReal.comp_continuousOn
    (cl.div hS.c1_lam.continuousOn (fun p hp => (hS.lam_pos p hp).ne'))
  have cR' := continuous_ofReal.comp_continuousOn
    (cn.div hS.c1_nu.continuousOn (fun p hp => (hS.nu_neg p hp).ne))
  have ha := eqOn_triangle_of_off_axis_aux hT
    (continuousOn_partial_u (c1_a_aux hS) (uniqueDiffOn_triangle hT))
    ((ca.sub (cR.mul cx)).sub cE) (fun p hp huv => by
      simpa only [pdU, pdV, Function.uncurry_def, Function.comp_apply, Pi.mul_apply,
        Pi.sub_apply, Pi.add_apply, Pi.neg_apply, Pi.div_apply, Prod.mk.eta,
        hq p.1 p.2 hp huv] using pdU_a_transport_aux hS hp.1 huv hp.2.2)
  have hb := eqOn_triangle_of_off_axis_aux hT
    (continuousOn_partial_v (c1_b_aux hS) (uniqueDiffOn_triangle hT))
    ((cR'.neg.mul cy).add cE') (fun p hp huv => by
      simpa only [pdU, pdV, Function.uncurry_def, Function.comp_apply, Pi.mul_apply,
        Pi.sub_apply, Pi.add_apply, Pi.neg_apply, Pi.div_apply, Prod.mk.eta,
        hq p.1 p.2 hp huv] using pdV_b_transport_aux hS hp.1 huv hp.2.2)
  have hp : (t, t) ∈ triangle 0 T := ⟨ht.1, le_rfl, ht.2⟩
  have hx : S.theta t t / S.lam t t = 0 := by
    simpa only [Fields.a, add_eq_left] using (hS.axis t hp).2.2.2.2.1
  have hy : S.xi t t / S.nu t t = 0 := by
    simpa only [Fields.b, add_eq_left] using (hS.axis t hp).2.2.2.2.2
  exact ⟨by simpa only [pdU, pdV, Function.uncurry_def, Function.comp_apply, Pi.mul_apply,
      Pi.sub_apply, Pi.add_apply, Pi.neg_apply, Pi.div_apply,
      hqaxis t ht, ofReal_zero, mul_zero, zero_mul, zero_div,
      hx, sub_zero, (hS.axis t hp).2.2.2.2.1] using ha hp,
    by simpa only [pdU, pdV, Function.uncurry_def, Function.comp_apply, Pi.mul_apply,
      Pi.sub_apply, Pi.add_apply, Pi.neg_apply, Pi.div_apply,
      hqaxis t ht, ofReal_zero, mul_zero, zero_mul, zero_div,
      hy, zero_add] using hb hp⟩

end EmcsfAcExtension.Local
