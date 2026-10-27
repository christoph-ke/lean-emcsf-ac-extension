module

public import EmcsfAcExtension.Local.Defs.C1Class
import EmcsfAcExtension.Local.Algebra.Normalized
import EmcsfAcExtension.Infra.Calculus.PartialsC1

/-! # Field-level normalized scalar transports

The quotient rule on closed characteristic sections supplies the derivative jets in the
algebraic cores. All identities hold off the axis, including the outer edges of the triangle.
The right sides are those of charged_SF_new_version.tex:L4326–4335.
-/

public section

open Set Complex

namespace EmcsfAcExtension.Local

/-- Incoming sectional derivative with the canonical domain partial. This local helper
avoids depending on the independently developed internal project record packet. -/
theorem hasDerivWithinAt_u_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T u v : ℝ} {f : ℝ → ℝ → E}
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) (triangle 0 T))
    (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    HasDerivWithinAt (fun s => f s v) (pdU (triangle 0 T) f u v) (Icc 0 v) u :=
  hasDerivWithinAt_uncurry_triangle_u hf ⟨hu, huv, hvT⟩

/-- Outgoing sectional derivative with the canonical domain partial; a local helper
for the parallel internal project record packet's sectional API. -/
theorem hasDerivWithinAt_v_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T u v : ℝ} {f : ℝ → ℝ → E}
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) (triangle 0 T))
    (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    HasDerivWithinAt (f u) (pdV (triangle 0 T) f u v) (Icc u T) v :=
  hasDerivWithinAt_uncurry_triangle_v hf ⟨hu, huv, hvT⟩

/-- The outgoing normalized scalar is C¹ on the full triangle, including the axis.
This helper uses the strict positivity of the outgoing expansion. -/
theorem c1_a_aux {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) :
    ContDiffOn ℝ 1 (Function.uncurry S.a) (triangle 0 T) := by
  have hl : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => (S.lam p.1 p.2 : ℂ)) (triangle 0 T) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hS.c1_lam
  simpa only [Fields.a, Function.uncurry_def, Pi.inv_apply, div_eq_mul_inv] using
    hS.c1_phi.add (hS.c1_theta.mul
    (hl.inv (fun p hp => Complex.ofReal_ne_zero.mpr (hS.lam_pos p hp).ne')))

/-- The incoming normalized scalar is C¹ on the full triangle, including the axis.
This helper uses the strict negativity of the incoming expansion. -/
theorem c1_b_aux {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) :
    ContDiffOn ℝ 1 (Function.uncurry S.b) (triangle 0 T) := by
  have hn : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => (S.nu p.1 p.2 : ℂ)) (triangle 0 T) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hS.c1_nu
  simpa only [Fields.b, Function.uncurry_def, Pi.inv_apply, div_eq_mul_inv] using
    hS.c1_phi.add (hS.c1_xi.mul
    (hn.inv (fun p hp => Complex.ofReal_ne_zero.mpr (hS.nu_neg p hp).ne)))

/-- [node restart-eq-normalized]
Incoming normalized transport, with the covariant connection moved to the ordinary
derivative's right side (charged_SF_new_version.tex:L4328–4330). No constants occur. -/
theorem eq_normalized_in {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    HasDerivWithinAt (fun s => S.a s v)
      (-(I * e * S.A u v * S.a u v) + (-(S.nu u v : ℂ) / S.r u v) *
        (((S.mu u v : ℂ) - S.Q u v ^ 2 / (S.r u v : ℂ) ^ 2) /
          (1 - S.mu u v) * (S.theta u v / S.lam u v) +
          I * e * S.Q u v * S.phi u v / (1 - S.mu u v))) (Icc 0 v) u := by
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have he := hS.eq_u (u, v) hp huv
  have hl : (S.lam u v : ℂ) ≠ 0 := by exact_mod_cast (hS.lam_pos _ hp).ne'
  have hd := (hasDerivWithinAt_u_aux hS.c1_phi hu huv.le hvT).add
    ((hasDerivWithinAt_u_aux hS.c1_theta hu huv.le hvT).div
      (hasDerivWithinAt_u_aux hS.c1_lam hu huv.le hvT).ofReal_comp hl)
  have ha := eq_normalized_in_algebra (r := S.r u v) (lam := S.lam u v)
    (nu := S.nu u v) (mu := S.mu u v) (Q := S.Q u v) (e := e) (A := S.A u v)
    (phi := S.phi u v) (theta := S.theta u v) (xi := S.xi u v)
    (hS.r_pos _ hp huv).ne' (hS.lam_pos _ hp).ne' (hS.one_sub_mu_pos _ hp).ne'
    he.2.1 he.2.2.2.2.1 he.2.2.2.2.2
  apply hd.congr_deriv
  rw [Fields.a]
  linear_combination ha

/-- [node restart-eq-normalized]
Outgoing normalized transport (charged_SF_new_version.tex:L4332–4335). The derivative and all
coefficients are literal, with no size or gauge assumption. -/
theorem eq_normalized_out {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    HasDerivWithinAt (S.b u)
      ((-(S.lam u v : ℂ) / S.r u v) *
        (((S.mu u v : ℂ) - S.Q u v ^ 2 / (S.r u v : ℂ) ^ 2) /
          (1 - S.mu u v) * (S.xi u v / S.nu u v) -
          I * e * S.Q u v * S.phi u v / (1 - S.mu u v))) (Icc u T) v := by
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have he := hS.eq_v (u, v) hp huv
  have hn : (S.nu u v : ℂ) ≠ 0 := by exact_mod_cast (hS.nu_neg _ hp).ne
  have hd := (hasDerivWithinAt_v_aux hS.c1_phi hu huv.le hvT).add
    ((hasDerivWithinAt_v_aux hS.c1_xi hu huv.le hvT).div
      (hasDerivWithinAt_v_aux hS.c1_nu hu huv.le hvT).ofReal_comp hn)
  apply hd.congr_deriv
  exact eq_normalized_out_algebra (r := S.r u v) (lam := S.lam u v)
    (nu := S.nu u v) (mu := S.mu u v) (Q := S.Q u v) (e := e)
    (phi := S.phi u v) (theta := S.theta u v) (xi := S.xi u v)
    (hS.r_pos _ hp huv).ne' (hS.nu_neg _ hp).ne (hS.one_sub_mu_pos _ hp).ne'
    he.2.1 he.2.2.2.2.2.1 he.2.2.2.2.2.2

end EmcsfAcExtension.Local
