module

public import EmcsfAcExtension.Local.Calculus.Normalized
public import EmcsfAcExtension.Local.Defs.Renormalized
import EmcsfAcExtension.Local.Algebra.Radial

/-! # Damped radial equations for the normalized scalar ratios

These are the exact field identities in charged_SF_new_version.tex:L5000–5010. The canonical
partials in `jC1` and `kC1` are identified by uniqueness of the sectional derivative.
-/

public section

open Set Complex

namespace EmcsfAcExtension.Local

/-- Outgoing quotient rule for `a`, expressed in the canonical domain partials. -/
theorem pdV_a_eq_aux {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    pdV (triangle 0 T) S.a u v = pdV (triangle 0 T) S.phi u v +
      (pdV (triangle 0 T) S.theta u v * S.lam u v -
        S.theta u v * pdV (triangle 0 T) S.lam u v) / (S.lam u v : ℂ) ^ 2 := by
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have hl : (S.lam u v : ℂ) ≠ 0 := by exact_mod_cast (hS.lam_pos _ hp).ne'
  have hd := (hasDerivWithinAt_v_aux hS.c1_phi hu huv.le hvT).add
    ((hasDerivWithinAt_v_aux hS.c1_theta hu huv.le hvT).div
      (hasDerivWithinAt_v_aux hS.c1_lam hu huv.le hvT).ofReal_comp hl)
  exact (uniqueDiffOn_Icc (huv.trans_le hvT) v ⟨huv.le, hvT⟩).eq_deriv _
    (hasDerivWithinAt_v_aux (c1_a_aux hS) hu huv.le hvT) hd

/-- Incoming quotient rule for `b`, expressed in the canonical domain partials. -/
theorem pdU_b_eq_aux {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    pdU (triangle 0 T) S.b u v = pdU (triangle 0 T) S.phi u v +
      (pdU (triangle 0 T) S.xi u v * S.nu u v -
        S.xi u v * pdU (triangle 0 T) S.nu u v) / (S.nu u v : ℂ) ^ 2 := by
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have hn : (S.nu u v : ℂ) ≠ 0 := by exact_mod_cast (hS.nu_neg _ hp).ne
  have hd := (hasDerivWithinAt_u_aux hS.c1_phi hu huv.le hvT).add
    ((hasDerivWithinAt_u_aux hS.c1_xi hu huv.le hvT).div
      (hasDerivWithinAt_u_aux hS.c1_nu hu huv.le hvT).ofReal_comp hn)
  exact (uniqueDiffOn_Icc (hu.trans_lt huv) u ⟨hu, huv.le⟩).eq_deriv _
    (hasDerivWithinAt_u_aux (c1_b_aux hS) hu huv.le hvT) hd

/-- [node restart-stab-out-reconstruction]
Exact outgoing damped radial equation (charged_SF_new_version.tex:L5000–5005). The ordinary
derivative is solved for on the right; no estimate or constant is introduced. -/
theorem stab_out_reconstruction {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    HasDerivWithinAt (fun s => S.theta u s / S.lam u s)
      (jC1 (triangle 0 T) S u v / (1 - S.mu u v) -
        (S.lam u v / S.r u v : ℝ) * (1 - ‖S.theta u v / S.lam u v‖ ^ 2) *
          (S.theta u v / S.lam u v)) (Icc u T) v := by
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have hl : (S.lam u v : ℂ) ≠ 0 := by exact_mod_cast (hS.lam_pos _ hp).ne'
  have hd := (hasDerivWithinAt_v_aux hS.c1_theta hu huv.le hvT).div
    (hasDerivWithinAt_v_aux hS.c1_lam hu huv.le hvT).ofReal_comp hl
  have ha := stab_out_reconstruction_algebra (r := S.r u v) (lam := S.lam u v)
    (mu := S.mu u v) (theta := S.theta u v) (j := jC1 (triangle 0 T) S u v)
    (phiV := pdV (triangle 0 T) S.phi u v)
    (ratioV := (pdV (triangle 0 T) S.theta u v * S.lam u v -
      S.theta u v * pdV (triangle 0 T) S.lam u v) / (S.lam u v : ℂ) ^ 2)
    (hS.r_pos _ hp huv).ne' (hS.lam_pos _ hp).ne' (hS.one_sub_mu_pos _ hp).ne'
    (hS.eq_v _ hp huv).2.2.2.2.2.1 (by
      simp only [jC1, pdV_a_eq_aux hS hu huv hvT, ofReal_div])
  apply hd.congr_deriv
  linear_combination ha

/-- [node restart-stab-in-reconstruction]
Exact incoming covariant damped radial equation (charged_SF_new_version.tex:L5006–5010),
with the connection term included in the ordinary derivative's right side. -/
theorem stab_in_reconstruction {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    HasDerivWithinAt (fun s => S.xi s v / S.nu s v)
      (kC1 e (triangle 0 T) S u v / (1 - S.mu u v) -
        I * e * S.A u v * (S.xi u v / S.nu u v) -
        (S.nu u v / S.r u v : ℝ) * (1 - ‖S.xi u v / S.nu u v‖ ^ 2) *
          (S.xi u v / S.nu u v)) (Icc 0 v) u := by
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have hn : (S.nu u v : ℂ) ≠ 0 := by exact_mod_cast (hS.nu_neg _ hp).ne
  have hd := (hasDerivWithinAt_u_aux hS.c1_xi hu huv.le hvT).div
    (hasDerivWithinAt_u_aux hS.c1_nu hu huv.le hvT).ofReal_comp hn
  have ha := stab_in_reconstruction_algebra (r := S.r u v) (nu := S.nu u v)
    (mu := S.mu u v) (e := e) (A := S.A u v) (phi := S.phi u v)
    (xi := S.xi u v) (k := kC1 e (triangle 0 T) S u v)
    (phiU := pdU (triangle 0 T) S.phi u v)
    (ratioU := (pdU (triangle 0 T) S.xi u v * S.nu u v -
      S.xi u v * pdU (triangle 0 T) S.nu u v) / (S.nu u v : ℂ) ^ 2)
    (hS.r_pos _ hp huv).ne' (hS.nu_neg _ hp).ne (hS.one_sub_mu_pos _ hp).ne'
    (hS.eq_u _ hp huv).2.2.2.2.1 (by
      simp only [kC1, Fields.b, pdU_b_eq_aux hS hu huv hvT, ofReal_div])
  apply hd.congr_deriv
  linear_combination ha

end EmcsfAcExtension.Local
