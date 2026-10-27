module

public import EmcsfAcExtension.Local.Calculus.KMixed
public import EmcsfAcExtension.Local.Defs.Renormalized
import EmcsfAcExtension.Local.Algebra.KTransport

/-! # Outgoing transport of the incoming renormalized scalar derivative

The covariant mixed jet is supplied by `KMixed`, including the positive Maxwell
commutator. All remaining differentiations are first-order sectional chain rules.
-/

public section

open Set Complex

namespace EmcsfAcExtension.Local

/-- [node restart-bv-k-trans]
The exact incoming renormalized derivative equation, charged_SF_new_version.tex:L4530–4532.
The outward derivative is ordinary in the fixed gauge `Aᵥ=0`. There is no axis-gauge,
smallness or higher differentiability hypothesis. -/
theorem bv_k_trans {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    HasDerivWithinAt (kC1 e (triangle 0 T) S u)
      (-(‖S.theta u v‖ ^ 2 / (S.lam u v * S.r u v)) * kC1 e (triangle 0 T) S u v +
        S.lam u v * S.xi u v / S.r u v ^ 2 *
          (starRingEnd ℂ (curv S u v) + 2 * curv S u v) + emSourceK e S u v) (Icc u T) v := by
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have he := hS.eq_v _ hp huv
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
  let bU : ℂ := pdU (triangle 0 T) S.b u v + I * e * S.A u v * S.b u v
  let nY : ℂ := (‖y‖ : ℂ) ^ 2
  let nZ : ℂ := (‖z‖ : ℂ) ^ 2
  let HU : ℂ := N / R * (B - H * nZ)
  let lamU : ℂ := L * N * B / (R * H)
  let cu : ℂ := -lamU / (R * H) + L * (N * H + R * HU) / (R * H) ^ 2
  let bu : ℂ := N / R * (H * nZ + Q ^ 2 / R ^ 2 - M) -
    2 * Q * S.QU e u v / R ^ 2 + 2 * Q ^ 2 * N / R ^ 3
  let dz : ℂ := -L / R * (y + B / H * z - g * Q / H * phi)
  let dzb : ℂ := -L / R * (starRingEnd ℂ y + B / H * starRingEnd ℂ z +
    g * Q / H * starRingEnd ℂ phi)
  let dH : ℂ := L / R * (B - H * nY)
  let dnr : ℂ := L * N / R ^ 2 * (B / H - 1)
  let dbU : ℂ := cu * (B * z - g * Q * phi) -
    L / (R * H) * (bu * z + B * (bU - N * z / R) -
      g * S.QU e u v * phi - g * Q * N * z / R) +
    g * (2 * L * N * Q / (H * R ^ 2)) * (phi + z)
  let K : ℂ := H * (bU - N / R * nZ * z)
  let C : ℂ := M + H * y * starRingEnd ℂ z
  let Ek : ℂ := (-N) * L / R ^ 2 *
    (5 * (Q ^ 2 / R ^ 2) * z - g * Q * (3 * z + phi)) +
    g * L * S.QU e u v * phi / R
  have hQU : S.QU e u v =
      e * S.r u v * S.nu u v * (starRingEnd ℂ phi * z).im := by
    dsimp only [Fields.QU, phi, z, N]
    rw [← mul_div_assoc, Complex.div_ofReal_im]
    field_simp [hn]
  have ha := bv_k_trans_complex (S.r u v) (S.lam u v) (S.nu u v) (S.mu u v)
    (S.Q u v) e y z phi bU hr hh
  dsimp only at ha
  rw [← hQU] at ha
  change dH * (bU - N / R * nZ * z) +
      H * (dbU - dnr * nZ * z - N / R *
        (dzb * z * z + 2 * starRingEnd ℂ z * z * dz)) =
    -L * nY / R * K + L * N * z / R ^ 2 * (starRingEnd ℂ C + 2 * C) + Ek at ha
  have dbu : HasDerivWithinAt
      (fun y => pdU (triangle 0 T) S.b u y + I * e * S.A u y * S.b u y)
      dbU (Icc u T) v := by
    apply (normalized_b_mixed_aux hS hu huv hvT).congr_deriv
    dsimp only [dbU, cu, lamU, HU, bu, B, H, M, R, L, N, Q, g, phi, z, nZ, bU]
    dsimp only [Fields.rUV, Fields.AV, Fields.b]
    push_cast
    field_simp [hrC, hhC]
    ring
  have dmu := Stab.outgoing_mu_derivative_identity hS hu huv hvT
  have dh : HasDerivWithinAt (fun y => ((1 - S.mu u y : ℝ) : ℂ)) dH (Icc u T) v := by
    apply (dmu.const_sub 1).ofReal_comp.congr_deriv
    dsimp only [dH, L, R, B, M, Q, H, nY]
    push_cast
    ring
  have dr : HasDerivWithinAt (S.r u) (S.lam u v) (Icc u T) v := by
    simpa only [he.1] using hasDerivWithinAt_v_aux hS.c1_r hu huv.le hvT
  have dn : HasDerivWithinAt (S.nu u) (S.rUV u v) (Icc u T) v := by
    simpa only [he.2.1] using hasDerivWithinAt_v_aux hS.c1_nu hu huv.le hvT
  have dcoef : HasDerivWithinAt (fun y => ((S.nu u y / S.r u y : ℝ) : ℂ))
      dnr (Icc u T) v := by
    apply (dn.div dr hr).ofReal_comp.congr_deriv
    dsimp only [dnr, N, L, R, B, M, Q, H, Fields.rUV]
    push_cast
    field_simp [hrC, hhC]
  have dphi := hasDerivWithinAt_v_aux hS.c1_phi hu huv.le hvT
  have dzf : HasDerivWithinAt (fun y => S.xi u y / S.nu u y) dz (Icc u T) v := by
    have h := (eq_normalized_out hS hu huv hvT).sub dphi
    have h' := h.congr (f₁ := fun y => S.xi u y / S.nu u y)
      (fun y _ => by simp only [Fields.b, Pi.sub_apply, add_sub_cancel_left])
      (by simp only [Fields.b, Pi.sub_apply, add_sub_cancel_left])
    apply h'.congr_deriv
    rw [he.2.2.2.2.2.1]
    dsimp only [dz, y, z, B, H, N, R, L, M, Q, phi, g, Fields.phiV]
    field_simp [hrC, hlC, hnC, hhC]
    ring
  have hconj : starRingEnd ℂ dz = dzb := by
    dsimp only [dz, dzb, g, L, R, B, M, Q, H, phi]
    simp only [map_add, map_sub, map_mul, map_div₀, map_neg, map_one, map_pow,
      Complex.conj_ofReal, Complex.conj_I]
    ring
  have dcubic := (dzf.star.mul dzf).mul dzf
  have hd := dh.mul (dbu.sub (dcoef.mul dcubic))
  have hd' := hd.congr (f₁ := kC1 e (triangle 0 T) S u)
    (fun y _ => by simp only [kC1, Pi.mul_apply, Pi.sub_apply, ofReal_sub, ofReal_one,
      ofReal_div, ← starRingEnd_apply, Complex.conj_mul']; ring)
    (by simp only [kC1, Pi.mul_apply, Pi.sub_apply, ofReal_sub, ofReal_one,
      ofReal_div, ← starRingEnd_apply, Complex.conj_mul']; ring)
  apply hd'.congr_deriv
  simp only [Pi.mul_apply, Pi.sub_apply, ofReal_sub, ofReal_one, ofReal_div,
    ← starRingEnd_apply, hconj, Complex.conj_mul']
  have hk : kC1 e (triangle 0 T) S u v = K := rfl
  have hc : curv S u v = C := by
    dsimp only [curv, C, M, H, y, z, L, N]
    simp only [map_div₀, Complex.conj_ofReal]
    field_simp [hlC, hnC]
  have helect : emSourceK e S u v = Ek := by
    dsimp only [emSourceK, Ek, N, L, R, Q, z, phi, g]
  have hhom : (-(‖S.theta u v‖ ^ 2 / (S.lam u v * S.r u v)) : ℂ) = -L * nY / R := by
    dsimp only [L, nY, y, R]
    have hy : ‖S.theta u v / S.lam u v‖ ^ 2 = ‖S.theta u v‖ ^ 2 / S.lam u v ^ 2 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, div_pow, sq_abs]
    have hyC : (‖S.theta u v / S.lam u v‖ : ℂ) ^ 2 =
        (‖S.theta u v‖ : ℂ) ^ 2 / (S.lam u v : ℂ) ^ 2 := by exact_mod_cast hy
    rw [hyC]
    field_simp [hrC, hlC]
  have hscalar : (S.lam u v : ℂ) * S.xi u v / (S.r u v : ℂ) ^ 2 =
      L * N * z / R ^ 2 := by
    dsimp only [N, L, z, R]
    field_simp [hnC]
  rw [hk, hc, helect, hhom, hscalar]
  dsimp only [K, nZ, z, N] at ha ⊢
  simp only [← Complex.conj_mul'] at ha ⊢
  linear_combination ha

end EmcsfAcExtension.Local
