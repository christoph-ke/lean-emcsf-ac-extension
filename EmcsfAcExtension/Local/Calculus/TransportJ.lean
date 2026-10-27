module

public import EmcsfAcExtension.Local.Calculus.JMixed
public import EmcsfAcExtension.Local.Defs.Renormalized
import EmcsfAcExtension.Local.Algebra.JTransport
import EmcsfAcExtension.Local.Algebra.Radial

/-! # Incoming transport of the outgoing renormalized scalar derivative

The mixed scalar jet is supplied by the integral representation in `JMixed`.
The remaining derivatives are first-order chain rules. The landed complex
algebraic core cancels the exact covariant cubic and Maxwell terms.
-/

public section

open Set Complex

namespace EmcsfAcExtension.Local

/-- [node restart-bv-j-trans]
The exact covariant outgoing renormalized transport, charged_SF_new_version.tex:L4526–4529.
The connection is moved to the ordinary derivative's right side, as in architecture
§3.1. No gauge, size or extra differentiability hypothesis is added. -/
theorem bv_j_trans {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    HasDerivWithinAt (fun x => jC1 (triangle 0 T) S x v)
      (-(I * e * S.A u v * jC1 (triangle 0 T) S u v) +
        (-(‖S.xi u v‖ ^ 2 / (S.nu u v * S.r u v)) * jC1 (triangle 0 T) S u v +
          S.nu u v * S.theta u v / S.r u v ^ 2 *
            (curv S u v + 2 * starRingEnd ℂ (curv S u v)) + emSourceJ e S u v)) (Icc 0 v) u := by
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have he := hS.eq_u _ hp huv
  have hr := (hS.r_pos _ hp huv).ne'
  have hl := (hS.lam_pos _ hp).ne'
  have hn := (hS.nu_neg _ hp).ne
  have hh := (hS.one_sub_mu_pos _ hp).ne'
  have hrC : (S.r u v : ℂ) ≠ 0 := by exact_mod_cast hr
  have hlC : (S.lam u v : ℂ) ≠ 0 := by exact_mod_cast hl
  have hnC : (S.nu u v : ℂ) ≠ 0 := by exact_mod_cast hn
  have hhC : 1 - (S.mu u v : ℂ) ≠ 0 := by exact_mod_cast hh
  let R : ℂ := S.r u v
  let L : ℂ := S.lam u v
  let N : ℂ := S.nu u v
  let M : ℂ := S.mu u v
  let Q : ℂ := S.Q u v
  let g : ℂ := I * e
  let H : ℂ := 1 - M
  let B : ℂ := M - Q ^ 2 / R ^ 2
  let y : ℂ := S.theta u v / L
  let z : ℂ := S.xi u v / N
  let phi : ℂ := S.phi u v
  let aV : ℂ := pdV (triangle 0 T) S.a u v
  let nY : ℂ := (‖y‖ : ℂ) ^ 2
  let nZ : ℂ := (‖z‖ : ℂ) ^ 2
  let conn : ℂ := g * S.A u v
  let HV : ℂ := L / R * (B - H * nY)
  let nuV : ℂ := N * L * B / (R * H)
  let cv : ℂ := -nuV / (R * H) + N * (L * H + R * HV) / (R * H) ^ 2
  let bv : ℂ := L / R * (H * nY + Q ^ 2 / R ^ 2 - M) -
    2 * Q * S.QV e u v / R ^ 2 + 2 * Q ^ 2 * L / R ^ 3
  let dy : ℂ := -N / R * (z + B / H * y + g * Q / H * phi)
  let dyb : ℂ := -N / R * (starRingEnd ℂ z + B / H * starRingEnd ℂ y -
    g * Q / H * starRingEnd ℂ phi)
  let dH : ℂ := N / R * (B - H * nZ)
  let dlr : ℂ := N * L / R ^ 2 * (B / H - 1)
  let daV : ℂ := cv * (B * y + g * Q * phi) -
    N / (R * H) * (bv * y + B * (aV - L * y / R) +
      g * S.QV e u v * phi + g * Q * L * y / R) -
    g * (2 * N * L * Q / (H * R ^ 2)) * (phi + y)
  let J : ℂ := H * (aV - L / R * nY * y)
  let C : ℂ := M + H * y * starRingEnd ℂ z
  let Ej : ℂ := (-N) * L / R ^ 2 *
    (5 * (Q ^ 2 / R ^ 2) * y + g * Q * (3 * y + phi)) -
    g * N * S.QV e u v * phi / R
  have hQV : S.QV e u v =
      -(e * S.r u v * S.lam u v * (starRingEnd ℂ phi * y).im) := by
    dsimp only [Fields.QV, phi, y, L]
    rw [← mul_div_assoc, Complex.div_ofReal_im]
    field_simp [hl]
  have ha := bv_j_trans_complex (S.r u v) (S.lam u v) (S.nu u v) (S.mu u v)
    (S.Q u v) e y z phi aV hr hh
  dsimp only at ha
  have hQVC : (S.QV e u v : ℂ) =
      -((e * S.r u v * S.lam u v * (starRingEnd ℂ phi * y).im : ℝ) : ℂ) := by
    exact_mod_cast hQV
  rw [← hQVC] at ha
  change dH * (aV - L / R * nY * y) +
      H * (daV - dlr * nY * y - L / R *
        (dyb * y * y + 2 * starRingEnd ℂ y * y * dy)) =
    -N * nZ / R * J + N * L * y / R ^ 2 * (C + 2 * starRingEnd ℂ C) + Ej at ha
  have dav : HasDerivWithinAt (fun x => pdV (triangle 0 T) S.a x v)
      (daV - conn * aV) (Icc 0 v) u := by
    apply (normalized_a_mixed_aux hS hu huv hvT).congr_deriv
    dsimp only [daV, cv, nuV, HV, bv, B, H, M, R, L, N, Q, g, phi, y, nY, aV, conn]
    dsimp only [Fields.rUV, Fields.AV, Fields.a]
    push_cast
    field_simp [hrC, hhC]
    ring
  have dmu : HasDerivWithinAt (fun x => S.mu x v)
      (S.nu u v / S.r u v * ((1 - S.mu u v) * ‖z‖ ^ 2 +
        S.Q u v ^ 2 / S.r u v ^ 2 - S.mu u v)) (Icc 0 v) u := by
    apply (hasDerivWithinAt_mu_u_aux hS hu huv hvT).congr_deriv
    exact Stab.outgoing_mu_derivative_identity_algebra hr hn he.2.2.1
  have dh : HasDerivWithinAt (fun x => ((1 - S.mu x v : ℝ) : ℂ)) dH (Icc 0 v) u := by
    apply (dmu.const_sub 1).ofReal_comp.congr_deriv
    dsimp only [dH, N, R, B, M, Q, H, nZ]
    push_cast
    ring
  have dr : HasDerivWithinAt (fun x => S.r x v) (S.nu u v) (Icc 0 v) u := by
    simpa only [he.1] using hasDerivWithinAt_u_aux hS.c1_r hu huv.le hvT
  have dl : HasDerivWithinAt (fun x => S.lam x v) (S.rUV u v) (Icc 0 v) u := by
    simpa only [he.2.1] using hasDerivWithinAt_u_aux hS.c1_lam hu huv.le hvT
  have dcoef : HasDerivWithinAt (fun x => ((S.lam x v / S.r x v : ℝ) : ℂ))
      dlr (Icc 0 v) u := by
    apply (dl.div dr hr).ofReal_comp.congr_deriv
    dsimp only [dlr, N, L, R, B, M, Q, H, Fields.rUV]
    push_cast
    field_simp [hrC, hhC]
  have dphi := hasDerivWithinAt_u_aux hS.c1_phi hu huv.le hvT
  have dyf : HasDerivWithinAt (fun x => S.theta x v / S.lam x v)
      (dy - conn * y) (Icc 0 v) u := by
    have h := (eq_normalized_in hS hu huv hvT).sub dphi
    have h' := h.congr (f₁ := fun x => S.theta x v / S.lam x v)
      (fun x _ => by simp only [Fields.a, Pi.sub_apply, add_sub_cancel_left])
      (by simp only [Fields.a, Pi.sub_apply, add_sub_cancel_left])
    apply h'.congr_deriv
    rw [he.2.2.2.2.1]
    dsimp only [dy, conn, y, z, B, H, N, R, L, M, Q, phi, g, Fields.a, Fields.phiU]
    field_simp [hrC, hlC, hnC, hhC]
    ring
  have hconj : starRingEnd ℂ (dy - conn * y) = dyb + conn * starRingEnd ℂ y := by
    dsimp only [dy, dyb, conn, g, N, R, B, M, Q, H, phi]
    simp only [map_add, map_sub, map_mul, map_div₀, map_neg, map_one, map_pow,
      Complex.conj_ofReal, Complex.conj_I]
    ring
  have dcubic := (dyf.star.mul dyf).mul dyf
  have hd := dh.mul (dav.sub (dcoef.mul dcubic))
  have hd' := hd.congr (f₁ := fun x => jC1 (triangle 0 T) S x v)
    (fun x _ => by simp only [jC1, Pi.mul_apply, Pi.sub_apply, ofReal_sub, ofReal_one,
      ofReal_div, ← starRingEnd_apply, Complex.conj_mul']; ring)
    (by simp only [jC1, Pi.mul_apply, Pi.sub_apply, ofReal_sub, ofReal_one,
      ofReal_div, ← starRingEnd_apply, Complex.conj_mul']; ring)
  apply hd'.congr_deriv
  simp only [Pi.mul_apply, Pi.sub_apply, ofReal_sub, ofReal_one, ofReal_div,
    ← starRingEnd_apply, hconj, Complex.conj_mul']
  have hj : jC1 (triangle 0 T) S u v = J := rfl
  have hc : curv S u v = C := by
    dsimp only [curv, C, M, H, y, z, L, N]
    simp only [map_div₀, Complex.conj_ofReal]
    field_simp [hlC, hnC]
  have helect : emSourceJ e S u v = Ej := by
    dsimp only [emSourceJ, Ej, N, L, R, Q, y, phi, g]
    ring
  have hhom : (-(‖S.xi u v‖ ^ 2 / (S.nu u v * S.r u v)) : ℂ) = -N * nZ / R := by
    dsimp only [N, nZ, z, R]
    have hz : ‖S.xi u v / S.nu u v‖ ^ 2 = ‖S.xi u v‖ ^ 2 / S.nu u v ^ 2 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, div_pow, sq_abs]
    have hzC : (‖S.xi u v / S.nu u v‖ : ℂ) ^ 2 =
        (‖S.xi u v‖ : ℂ) ^ 2 / (S.nu u v : ℂ) ^ 2 := by exact_mod_cast hz
    rw [hzC]
    field_simp [hrC, hnC]
  have hscalar : (S.nu u v : ℂ) * S.theta u v / (S.r u v : ℂ) ^ 2 =
      N * L * y / R ^ 2 := by
    dsimp only [N, L, y, R]
    field_simp [hlC]
  rw [hj, hc, helect, hhom, hscalar]
  change _ = -(conn * J) + (-N * nZ / R * J +
    N * L * y / R ^ 2 * (C + 2 * starRingEnd ℂ C) + Ej)
  dsimp only [J, nY, y, L] at ha ⊢
  simp only [← Complex.conj_mul'] at ha ⊢
  linear_combination ha

end EmcsfAcExtension.Local
