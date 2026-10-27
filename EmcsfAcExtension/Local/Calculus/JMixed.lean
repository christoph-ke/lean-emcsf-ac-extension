module

public import EmcsfAcExtension.Local.Calculus.RadialIdentity
public import EmcsfAcExtension.Local.Calculus.Raychaudhuri
import EmcsfAcExtension.Local.Calculus.TransportRegularity
import EmcsfAcExtension.Local.Calculus.OffAxisMixed

/-! # Incoming derivative of the outgoing normalized scalar partial

The mixed derivative is recovered from the characteristic integral representation.
The displayed jet is obtained by differentiating only the prescribed incoming source
in the outgoing direction. It assumes no C² regularity of the scalar field.
-/

public section

open Set Complex

namespace EmcsfAcExtension.Local

/-- The exact mixed jet used in the outgoing renormalized transport. The `C`,
`CV`, `BV` abbreviations describe the ordinary quotient and product rules for
`-ν/(r(1-μ))` and `μ-Q²/r²`. The mixed partial itself is obtained by integration. -/
theorem normalized_a_mixed_aux {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    let r : ℝ := S.r u v
    let L : ℝ := S.lam u v
    let N : ℝ := S.nu u v
    let H : ℝ := 1 - S.mu u v
    let B : ℝ := S.mu u v - S.Q u v ^ 2 / r ^ 2
    let y : ℂ := S.theta u v / L
    let aV : ℂ := pdV (triangle 0 T) S.a u v
    let HV : ℝ := L / r * (B - H * ‖y‖ ^ 2)
    let CV : ℝ := -S.rUV u v / (r * H) + N * (L * H + r * HV) / (r * H) ^ 2
    let BV : ℝ := L / r * (H * ‖y‖ ^ 2 + S.Q u v ^ 2 / r ^ 2 - S.mu u v) -
      2 * S.Q u v * S.QV e u v / r ^ 2 + 2 * S.Q u v ^ 2 * L / r ^ 3
    HasDerivWithinAt (fun x => pdV (triangle 0 T) S.a x v)
      (-(I * e * S.AV u v * S.a u v + I * e * S.A u v * aV) +
        (CV : ℂ) * ((B : ℂ) * y + I * e * S.Q u v * S.phi u v) +
        ((-N / (r * H) : ℝ) : ℂ) *
          ((BV : ℂ) * y + (B : ℂ) * (aV - L * y / r) +
            I * e * S.QV e u v * S.phi u v + I * e * S.Q u v * (L * y / r))) (Icc 0 v) u := by
  let G (x y : ℝ) : ℂ := -(I * e * S.A x y * S.a x y) +
    ((-S.nu x y / (S.r x y * (1 - S.mu x y)) : ℝ) : ℂ) *
      (((S.mu x y - S.Q x y ^ 2 / S.r x y ^ 2 : ℝ) : ℂ) *
        (S.theta x y / S.lam x y) + I * e * S.Q x y * S.phi x y)
  have cG : ContDiffOn ℝ 1 (Function.uncurry G)
      {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ T} := c1_normalized_source_in_aux hS
  have htrans (x y : ℝ) (hx : 0 ≤ x) (hxy : x < y) (hy : y ≤ T) :
      pdU (triangle 0 T) S.a x y = G x y := by
    have hp : (x, y) ∈ triangle 0 T := ⟨hx, hxy.le, hy⟩
    have he := (uniqueDiffOn_Icc (hx.trans_lt hxy) x ⟨hx, hxy.le⟩).eq_deriv _
      (hasDerivWithinAt_u_aux (c1_a_aux hS) hx hxy.le hy) (eq_normalized_in hS hx hxy hy)
    rw [he]
    dsimp only [G]
    have hr : (S.r x y : ℂ) ≠ 0 := by exact_mod_cast (hS.r_pos _ hp hxy).ne'
    have hm : 1 - (S.mu x y : ℂ) ≠ 0 := by exact_mod_cast (hS.one_sub_mu_pos _ hp).ne'
    push_cast
    field_simp [hr, hm]
  have hmixed := mixed_u_pdV_triangle_of_c1_transport_aux (c1_a_aux hS) cG htrans hu huv hvT
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have he := hS.eq_v _ hp huv
  have hr := (hS.r_pos _ hp huv).ne'
  have hl := (hS.lam_pos _ hp).ne'
  have hh := (hS.one_sub_mu_pos _ hp).ne'
  have hrC : (S.r u v : ℂ) ≠ 0 := by exact_mod_cast hr
  have hlC : (S.lam u v : ℂ) ≠ 0 := by exact_mod_cast hl
  let H : ℝ := 1 - S.mu u v
  let B : ℝ := S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2
  let y : ℂ := S.theta u v / S.lam u v
  let HV : ℝ := S.lam u v / S.r u v * (B - H * ‖y‖ ^ 2)
  let CV : ℝ := -S.rUV u v / (S.r u v * H) +
    S.nu u v * (S.lam u v * H + S.r u v * HV) / (S.r u v * H) ^ 2
  let BV : ℝ := S.lam u v / S.r u v *
    (H * ‖y‖ ^ 2 + S.Q u v ^ 2 / S.r u v ^ 2 - S.mu u v) -
    2 * S.Q u v * S.QV e u v / S.r u v ^ 2 +
    2 * S.Q u v ^ 2 * S.lam u v / S.r u v ^ 3
  have dr : HasDerivWithinAt (S.r u) (S.lam u v) (Icc u T) v := by
    simpa only [he.1] using hasDerivWithinAt_v_aux hS.c1_r hu huv.le hvT
  have dn : HasDerivWithinAt (S.nu u) (S.rUV u v) (Icc u T) v := by
    simpa only [he.2.1] using hasDerivWithinAt_v_aux hS.c1_nu hu huv.le hvT
  have dq : HasDerivWithinAt (S.Q u) (S.QV e u v) (Icc u T) v := by
    simpa only [he.2.2.2.1] using hasDerivWithinAt_v_aux hS.c1_Q hu huv.le hvT
  have dA : HasDerivWithinAt (S.A u) (S.AV u v) (Icc u T) v := by
    simpa only [he.2.2.2.2.1] using hasDerivWithinAt_v_aux hS.c1_A hu huv.le hvT
  have dm := Stab.outgoing_mu_derivative_identity hS hu huv hvT
  have dH : HasDerivWithinAt (fun s => 1 - S.mu u s) HV (Icc u T) v := by
    apply (dm.const_sub 1).congr_deriv
    dsimp only [HV, B, H, y]
    ring
  have dC : HasDerivWithinAt (fun s => -S.nu u s / (S.r u s * (1 - S.mu u s)))
      CV (Icc u T) v := by
    apply (dn.neg.div (dr.mul dH) (mul_ne_zero hr hh)).congr_deriv
    dsimp only [CV, H]
    simp only [Pi.mul_apply, Pi.neg_apply]
    field_simp [hr, hh]
    ring
  have dB : HasDerivWithinAt (fun s => S.mu u s - S.Q u s ^ 2 / S.r u s ^ 2)
      BV (Icc u T) v := by
    apply (dm.sub ((dq.pow 2).div (dr.pow 2) (pow_ne_zero 2 hr))).congr_deriv
    dsimp only [BV, H, y]
    simp only [Pi.pow_apply]
    field_simp [hr]
    ring
  have dY : HasDerivWithinAt (fun s => S.theta u s / S.lam u s)
      (pdV (triangle 0 T) S.a u v - S.lam u v * y / S.r u v) (Icc u T) v := by
    apply ((hasDerivWithinAt_v_aux hS.c1_theta hu huv.le hvT).div
      (hasDerivWithinAt_v_aux hS.c1_lam hu huv.le hvT).ofReal_comp hlC).congr_deriv
    rw [pdV_a_eq_aux hS hu huv hvT, he.2.2.2.2.2.1]
    dsimp only [Fields.phiV, y]
    field_simp [hrC, hlC]
    ring
  have dp : HasDerivWithinAt (S.phi u) (S.lam u v * y / S.r u v) (Icc u T) v := by
    apply (hasDerivWithinAt_v_aux hS.c1_phi hu huv.le hvT).congr_deriv
    rw [he.2.2.2.2.2.1]
    dsimp only [Fields.phiV, y]
    field_simp [hrC, hlC]
  have da := hasDerivWithinAt_v_aux (c1_a_aux hS) hu huv.le hvT
  have dG := (((dA.ofReal_comp.const_mul (I * e)).mul da).neg).add
    (dC.ofReal_comp.mul ((dB.ofReal_comp.mul dY).add
      ((dq.ofReal_comp.const_mul (I * e)).mul dp)))
  have dG' := dG.congr (f₁ := G u)
    (fun s _ => by simp only [G, Pi.add_apply, Pi.mul_apply, Pi.neg_apply])
    (by simp only [G, Pi.add_apply, Pi.mul_apply, Pi.neg_apply])
  have hjet := (uniqueDiffOn_Icc (huv.trans_le hvT) v ⟨huv.le, hvT⟩).eq_deriv _
    (hasDerivWithinAt_off_triangle_v_aux cG hu huv hvT) dG'
  rw [hjet] at hmixed
  dsimp only [CV, BV, HV, H, B, y] at hmixed ⊢
  convert hmixed using 1
  simp only [Pi.mul_apply, Pi.add_apply]
  push_cast
  ring

end EmcsfAcExtension.Local
