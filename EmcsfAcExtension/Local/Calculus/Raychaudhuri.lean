module

public import EmcsfAcExtension.Local.Calculus.Normalized
import EmcsfAcExtension.Local.Algebra.Raychaudhuri
import EmcsfAcExtension.Local.Algebra.Radial

/-! # Raychaudhuri and mass-ratio identities on the classical class

All derivatives are taken within the complete closed characteristic section. Radius
positivity excludes the axis; no small-data or axis-gauge hypothesis is needed.
-/

public section

open Set

namespace EmcsfAcExtension.Local

/-- Differentiate the literal mass ratio on an incoming section. The derivative is
written in the form used by the Raychaudhuri algebraic core. -/
theorem hasDerivWithinAt_mu_u_aux {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    HasDerivWithinAt (fun s => S.mu s v)
      (2 * pdU (triangle 0 T) S.m u v / S.r u v -
        2 * S.m u v * S.nu u v / S.r u v ^ 2) (Icc 0 v) u := by
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have hr := hasDerivWithinAt_u_aux hS.c1_r hu huv.le hvT
  rw [(hS.eq_u _ hp huv).1] at hr
  apply (((hasDerivWithinAt_u_aux hS.c1_m hu huv.le hvT).const_mul 2).div
    hr (hS.r_pos _ hp huv).ne').congr_deriv
  field_simp

/-- Differentiate the literal mass ratio on an outgoing section. This local helper
uses only the C¹ field class and the radius equation. -/
theorem hasDerivWithinAt_mu_v_aux {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    HasDerivWithinAt (S.mu u)
      (2 * pdV (triangle 0 T) S.m u v / S.r u v -
        2 * S.m u v * S.lam u v / S.r u v ^ 2) (Icc u T) v := by
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have hr := hasDerivWithinAt_v_aux hS.c1_r hu huv.le hvT
  rw [(hS.eq_v _ hp huv).1] at hr
  apply (((hasDerivWithinAt_v_aux hS.c1_m hu huv.le hvT).const_mul 2).div
    hr (hS.r_pos _ hp huv).ne').congr_deriv
  field_simp

/-- [node restart-sec-bv-stability-independent#outgoing-mu-derivative-identity]
The exact outgoing mass-ratio derivative, charged_SF_new_version.tex:L5444–5448.
There are no constants; the identity holds on the full off-axis classical class. -/
theorem Stab.outgoing_mu_derivative_identity {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    HasDerivWithinAt (S.mu u)
      (S.lam u v / S.r u v * ((1 - S.mu u v) * ‖S.theta u v / S.lam u v‖ ^ 2 +
        S.Q u v ^ 2 / S.r u v ^ 2 - S.mu u v)) (Icc u T) v := by
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  apply (hasDerivWithinAt_mu_v_aux hS hu huv hvT).congr_deriv
  exact outgoing_mu_derivative_identity_algebra (hS.r_pos _ hp huv).ne'
    (hS.lam_pos _ hp).ne' (hS.eq_v _ hp huv).2.2.1

/-- [node restart-eq-ray]
Incoming Raychaudhuri identity, charged_SF_new_version.tex:L4336. Exact coefficients, with no
smallness or gauge hypothesis. -/
theorem eq_ray_in {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    HasDerivWithinAt (fun s => Real.log (S.lam s v / (1 - S.mu s v)))
      (‖S.xi u v‖ ^ 2 / (S.nu u v * S.r u v)) (Icc 0 v) u := by
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have hr := (hS.r_pos _ hp huv).ne'
  have hl := (hS.lam_pos _ hp).ne'
  have hn := (hS.nu_neg _ hp).ne
  have hm := (hS.one_sub_mu_pos _ hp).ne'
  have hmu := hasDerivWithinAt_mu_u_aux hS hu huv hvT
  have hd := ((hasDerivWithinAt_u_aux hS.c1_lam hu huv.le hvT).div
    (hmu.const_sub 1) hm).log (div_ne_zero hl hm)
  apply hd.congr_deriv
  have ha := eq_ray_in_algebra hr hl hn hm
    (hS.eq_u _ hp huv).2.1 (hS.eq_u _ hp huv).2.2.1
  calc
    _ = pdU (triangle 0 T) S.lam u v / S.lam u v +
        (2 * pdU (triangle 0 T) S.m u v / S.r u v -
          2 * S.m u v * S.nu u v / S.r u v ^ 2) / (1 - S.mu u v) := by
      simp only [Pi.div_apply]
      field_simp [hl, hm]
      ring
    _ = _ := ha

/-- [node restart-eq-ray]
Outgoing Raychaudhuri identity, charged_SF_new_version.tex:L4336, with `-ν` inside the logarithm.
The coefficient on the right is exactly the paper's quadratic flux. -/
theorem eq_ray_out {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    HasDerivWithinAt (fun s => Real.log (-S.nu u s / (1 - S.mu u s)))
      (‖S.theta u v‖ ^ 2 / (S.lam u v * S.r u v)) (Icc u T) v := by
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have hr := (hS.r_pos _ hp huv).ne'
  have hl := (hS.lam_pos _ hp).ne'
  have hn := (hS.nu_neg _ hp).ne
  have hm := (hS.one_sub_mu_pos _ hp).ne'
  have hmu := hasDerivWithinAt_mu_v_aux hS hu huv hvT
  have hd := ((hasDerivWithinAt_v_aux hS.c1_nu hu huv.le hvT).neg.div
    (hmu.const_sub 1) hm).log (div_ne_zero (neg_ne_zero.mpr hn) hm)
  apply hd.congr_deriv
  have ha := eq_ray_out_algebra hr hl hn hm
    (hS.eq_v _ hp huv).2.1 (hS.eq_v _ hp huv).2.2.1
  calc
    _ = pdV (triangle 0 T) S.nu u v / S.nu u v +
        (2 * pdV (triangle 0 T) S.m u v / S.r u v -
          2 * S.m u v * S.lam u v / S.r u v ^ 2) / (1 - S.mu u v) := by
      simp only [Pi.div_apply, Pi.neg_apply]
      field_simp [hn, hm]
      ring
    _ = _ := ha

end EmcsfAcExtension.Local
