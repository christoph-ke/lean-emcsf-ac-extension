module

public import EmcsfAcExtension.Local.Calculus.RadialIdentity
public import EmcsfAcExtension.Local.Calculus.Raychaudhuri
import EmcsfAcExtension.Local.Calculus.TransportRegularity
import EmcsfAcExtension.Local.Calculus.OffAxisMixed
import EmcsfAcExtension.Local.Algebra.Radial

/-! # Outgoing derivative of the incoming covariant scalar partial

The ordinary mixed partial is obtained by integration of the outgoing transport.
Differentiating the connection separately then gives the positive commutator sign.
-/

public section

open Set Complex

namespace EmcsfAcExtension.Local

/-- The covariant mixed jet for the incoming renormalized transport. Its final
`ie Aᵥ b` term is the commutator, with positive sign. Only the outgoing normalized
source is differentiated; the mixed partial comes from its integral representation. -/
theorem normalized_b_mixed_aux {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    let r : ℝ := S.r u v
    let L : ℝ := S.lam u v
    let N : ℝ := S.nu u v
    let H : ℝ := 1 - S.mu u v
    let B : ℝ := S.mu u v - S.Q u v ^ 2 / r ^ 2
    let z : ℂ := S.xi u v / N
    let bU : ℂ := pdU (triangle 0 T) S.b u v + I * e * S.A u v * S.b u v
    let HU : ℝ := N / r * (B - H * ‖z‖ ^ 2)
    let CU : ℝ := -S.rUV u v / (r * H) + L * (N * H + r * HU) / (r * H) ^ 2
    let BU : ℝ := N / r * (H * ‖z‖ ^ 2 + S.Q u v ^ 2 / r ^ 2 - S.mu u v) -
      2 * S.Q u v * S.QU e u v / r ^ 2 + 2 * S.Q u v ^ 2 * N / r ^ 3
    HasDerivWithinAt (fun y => pdU (triangle 0 T) S.b u y + I * e * S.A u y * S.b u y)
      ((CU : ℂ) * ((B : ℂ) * z - I * e * S.Q u v * S.phi u v) +
        ((-L / (r * H) : ℝ) : ℂ) *
          ((BU : ℂ) * z + (B : ℂ) * (bU - N * z / r) -
            I * e * S.QU e u v * S.phi u v - I * e * S.Q u v * (N * z / r)) +
        I * e * S.AV u v * S.b u v) (Icc u T) v := by
  let G (x y : ℝ) : ℂ := ((-S.lam x y / (S.r x y * (1 - S.mu x y)) : ℝ) : ℂ) *
    (((S.mu x y - S.Q x y ^ 2 / S.r x y ^ 2 : ℝ) : ℂ) *
      (S.xi x y / S.nu x y) - I * e * S.Q x y * S.phi x y)
  have cG : ContDiffOn ℝ 1 (Function.uncurry G)
      {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ T} := c1_normalized_source_out_aux hS
  have htrans (x y : ℝ) (hx : 0 ≤ x) (hxy : x < y) (hy : y ≤ T) :
      pdV (triangle 0 T) S.b x y = G x y := by
    have hp : (x, y) ∈ triangle 0 T := ⟨hx, hxy.le, hy⟩
    have he := (uniqueDiffOn_Icc (hxy.trans_le hy) y ⟨hxy.le, hy⟩).eq_deriv _
      (hasDerivWithinAt_v_aux (c1_b_aux hS) hx hxy.le hy) (eq_normalized_out hS hx hxy hy)
    rw [he]
    dsimp only [G]
    have hr : (S.r x y : ℂ) ≠ 0 := by exact_mod_cast (hS.r_pos _ hp hxy).ne'
    have hm : 1 - (S.mu x y : ℂ) ≠ 0 := by exact_mod_cast (hS.one_sub_mu_pos _ hp).ne'
    push_cast
    field_simp [hr, hm]
  have hmixed := mixed_v_pdU_triangle_of_c1_transport_aux (c1_b_aux hS) cG htrans hu huv hvT
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have he := hS.eq_u _ hp huv
  have hr := (hS.r_pos _ hp huv).ne'
  have hn := (hS.nu_neg _ hp).ne
  have hh := (hS.one_sub_mu_pos _ hp).ne'
  have hrC : (S.r u v : ℂ) ≠ 0 := by exact_mod_cast hr
  have hnC : (S.nu u v : ℂ) ≠ 0 := by exact_mod_cast hn
  let H : ℝ := 1 - S.mu u v
  let B : ℝ := S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2
  let z : ℂ := S.xi u v / S.nu u v
  let bU : ℂ := pdU (triangle 0 T) S.b u v + I * e * S.A u v * S.b u v
  let HU : ℝ := S.nu u v / S.r u v * (B - H * ‖z‖ ^ 2)
  let CU : ℝ := -S.rUV u v / (S.r u v * H) +
    S.lam u v * (S.nu u v * H + S.r u v * HU) / (S.r u v * H) ^ 2
  let BU : ℝ := S.nu u v / S.r u v *
    (H * ‖z‖ ^ 2 + S.Q u v ^ 2 / S.r u v ^ 2 - S.mu u v) -
    2 * S.Q u v * S.QU e u v / S.r u v ^ 2 +
    2 * S.Q u v ^ 2 * S.nu u v / S.r u v ^ 3
  have dr : HasDerivWithinAt (fun x => S.r x v) (S.nu u v) (Icc 0 v) u := by
    simpa only [he.1] using hasDerivWithinAt_u_aux hS.c1_r hu huv.le hvT
  have dl : HasDerivWithinAt (fun x => S.lam x v) (S.rUV u v) (Icc 0 v) u := by
    simpa only [he.2.1] using hasDerivWithinAt_u_aux hS.c1_lam hu huv.le hvT
  have dq : HasDerivWithinAt (fun x => S.Q x v) (S.QU e u v) (Icc 0 v) u := by
    simpa only [he.2.2.2.1] using hasDerivWithinAt_u_aux hS.c1_Q hu huv.le hvT
  have dm : HasDerivWithinAt (fun x => S.mu x v)
      (S.nu u v / S.r u v * ((1 - S.mu u v) * ‖z‖ ^ 2 +
        S.Q u v ^ 2 / S.r u v ^ 2 - S.mu u v)) (Icc 0 v) u := by
    apply (hasDerivWithinAt_mu_u_aux hS hu huv hvT).congr_deriv
    exact Stab.outgoing_mu_derivative_identity_algebra hr hn he.2.2.1
  have dH : HasDerivWithinAt (fun x => 1 - S.mu x v) HU (Icc 0 v) u := by
    apply (dm.const_sub 1).congr_deriv
    dsimp only [HU, B, H]
    ring
  have dC : HasDerivWithinAt (fun x => -S.lam x v / (S.r x v * (1 - S.mu x v)))
      CU (Icc 0 v) u := by
    apply (dl.neg.div (dr.mul dH) (mul_ne_zero hr hh)).congr_deriv
    dsimp only [CU, H]
    simp only [Pi.mul_apply, Pi.neg_apply]
    field_simp [hr, hh]
    ring
  have dB : HasDerivWithinAt (fun x => S.mu x v - S.Q x v ^ 2 / S.r x v ^ 2)
      BU (Icc 0 v) u := by
    apply (dm.sub ((dq.pow 2).div (dr.pow 2) (pow_ne_zero 2 hr))).congr_deriv
    dsimp only [BU, H]
    simp only [Pi.pow_apply]
    field_simp [hr]
    ring
  have dZ : HasDerivWithinAt (fun x => S.xi x v / S.nu x v)
      (bU - S.nu u v * z / S.r u v - I * e * S.A u v * z) (Icc 0 v) u := by
    apply ((hasDerivWithinAt_u_aux hS.c1_xi hu huv.le hvT).div
      (hasDerivWithinAt_u_aux hS.c1_nu hu huv.le hvT).ofReal_comp hnC).congr_deriv
    dsimp only [bU]
    rw [pdU_b_eq_aux hS hu huv hvT, he.2.2.2.2.1]
    dsimp only [Fields.phiU, Fields.b, z]
    field_simp [hrC, hnC]
    ring
  have dp : HasDerivWithinAt (fun x => S.phi x v)
      (S.nu u v * z / S.r u v - I * e * S.A u v * S.phi u v) (Icc 0 v) u := by
    apply (hasDerivWithinAt_u_aux hS.c1_phi hu huv.le hvT).congr_deriv
    rw [he.2.2.2.2.1]
    dsimp only [Fields.phiU, z]
    field_simp [hrC, hnC]
  have dG := dC.ofReal_comp.mul ((dB.ofReal_comp.mul dZ).sub
    ((dq.ofReal_comp.const_mul (I * e)).mul dp))
  have dG' := dG.congr (f₁ := fun x => G x v)
    (fun x _ => by simp only [G, Pi.mul_apply, Pi.sub_apply])
    (by simp only [G, Pi.mul_apply, Pi.sub_apply])
  have hjet := (uniqueDiffOn_Icc (hu.trans_lt huv) u ⟨hu, huv.le⟩).eq_deriv _
    (hasDerivWithinAt_off_triangle_u_aux cG hu huv hvT) dG'
  rw [hjet] at hmixed
  have dAv : HasDerivWithinAt (S.A u) (S.AV u v) (Icc u T) v := by
    simpa only [(hS.eq_v _ hp huv).2.2.2.2.1] using
      hasDerivWithinAt_v_aux hS.c1_A hu huv.le hvT
  have dbv := hasDerivWithinAt_v_aux (c1_b_aux hS) hu huv.le hvT
  rw [htrans u v hu huv hvT] at dbv
  have hd := hmixed.add ((dAv.ofReal_comp.const_mul (I * e)).mul dbv)
  dsimp only [CU, BU, HU, H, B, z, bU] at hd ⊢
  convert hd using 1
  simp only [Pi.mul_apply, Pi.sub_apply, G]
  push_cast
  ring

end EmcsfAcExtension.Local
