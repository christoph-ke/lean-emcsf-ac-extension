module

public import EmcsfAcExtension.Local.Calculus.RadialIdentity
public import EmcsfAcExtension.Local.Calculus.Raychaudhuri
import EmcsfAcExtension.Local.Algebra.Curvature

/-! # Exact curvature primitive equations on the classical class

Product, conjugation and quotient rules supply the first derivative jets for the
algebraic curvature cores, charged_SF_new_version.tex:L4533–4538. No mixed derivative occurs.
-/

public section

open Set Complex

namespace EmcsfAcExtension.Local

/-- [node restart-bv-C-v]
The outgoing curvature primitive equation, with every coefficient as in
charged_SF_new_version.tex:L4533–4535. It holds at every off-axis point of the closed triangle. -/
theorem bv_c_v {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    HasDerivWithinAt (fun s => (S.r u s : ℂ) * curv S u s)
      ((S.r u v : ℂ) * (starRingEnd ℂ (S.xi u v) / S.nu u v) *
        jC1 (triangle 0 T) S u v +
        (S.lam u v * S.Q u v ^ 2 / S.r u v ^ 2 : ℝ) -
        I * e * S.Q u v * S.theta u v * starRingEnd ℂ (S.phi u v)) (Icc u T) v := by
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have he := hS.eq_v _ hp huv
  have hr := (hS.r_pos _ hp huv).ne'
  have hl := (hS.lam_pos _ hp).ne'
  have hn := (hS.nu_neg _ hp).ne
  have hm := (hS.one_sub_mu_pos _ hp).ne'
  have hrC : (S.r u v : ℂ) ≠ 0 := by exact_mod_cast hr
  have hlC : (S.lam u v : ℂ) ≠ 0 := by exact_mod_cast hl
  have hnC : (S.nu u v : ℂ) ≠ 0 := by exact_mod_cast hn
  have hmC : 1 - (S.mu u v : ℂ) ≠ 0 := by exact_mod_cast hm
  have dr := hasDerivWithinAt_v_aux hS.c1_r hu huv.le hvT
  have dl := hasDerivWithinAt_v_aux hS.c1_lam hu huv.le hvT
  have dn := hasDerivWithinAt_v_aux hS.c1_nu hu huv.le hvT
  have dt := hasDerivWithinAt_v_aux hS.c1_theta hu huv.le hvT
  have dx := hasDerivWithinAt_v_aux hS.c1_xi hu huv.le hvT
  have dm := hasDerivWithinAt_mu_v_aux hS hu huv hvT
  have dc := dm.ofReal_comp.add
    ((((dm.const_sub 1).ofReal_comp.mul dt).mul dx.star).div
      (dl.ofReal_comp.mul dn.ofReal_comp) (mul_ne_zero hlC hnC))
  have hd := dr.ofReal_comp.mul dc
  have hd' := hd.congr (f₁ := fun s => (S.r u s : ℂ) * curv S u s)
    (fun s _ => by simp only [curv, Pi.mul_apply, Pi.div_apply, Pi.add_apply,
      ofReal_sub, ofReal_one, ← starRingEnd_apply])
    (by simp only [curv, Pi.mul_apply, Pi.div_apply, Pi.add_apply,
      ofReal_sub, ofReal_one, ← starRingEnd_apply])
  apply hd'.congr_deriv
  simp only [Pi.mul_apply, Pi.div_apply, Pi.add_apply]
  have ha := bv_c_v_algebra (S.r u v : ℂ) (S.lam u v : ℂ) (S.nu u v : ℂ)
    (S.mu u v : ℂ) (S.Q u v : ℂ) (I * e)
    (S.theta u v) (starRingEnd ℂ (S.theta u v)) (starRingEnd ℂ (S.xi u v))
    (starRingEnd ℂ (S.phi u v)) (pdV (triangle 0 T) S.theta u v)
    ((pdV (triangle 0 T) S.lam u v : ℝ) : ℂ) hrC hlC hnC hmC
  dsimp only at ha
  rw [jC1, pdV_a_eq_aux hS hu huv hvT]
  rw [he.1, he.2.1, he.2.2.1, he.2.2.2.2.2.1, he.2.2.2.2.2.2]
  dsimp only [Fields.mV, Fields.rUV, Fields.phiV, Fields.xiV, Fields.waveSource]
  have hnorm : ‖S.theta u v / S.lam u v‖ ^ 2 = ‖S.theta u v‖ ^ 2 / S.lam u v ^ 2 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, div_pow, sq_abs]
  have hnormC : (‖S.theta u v / S.lam u v‖ : ℂ) ^ 2 =
      (‖S.theta u v‖ : ℂ) ^ 2 / (S.lam u v : ℂ) ^ 2 := by exact_mod_cast hnorm
  rw [hnormC]
  push_cast
  simp only [starRingEnd_apply, star_add, star_mul, star_div₀, star_neg, star_sub]
  simp only [← starRingEnd_apply, map_one, Complex.conj_ofReal, Complex.conj_I]
  simp only [← Complex.conj_mul']
  dsimp only [Fields.mu] at ha hmC ⊢
  push_cast at ha hmC ⊢
  have hdenC : (S.r u v : ℂ) - 2 * (S.m u v : ℂ) ≠ 0 := by
    intro hz
    apply hmC
    field_simp [hrC]
    linear_combination hz
  convert ha using 1 <;> field_simp [hrC, hlC, hnC, hmC, hdenC] <;> ring

/-- The conjugate curvature written in the incoming orientation. The identity
is algebraic and valid also at the literal total-function axis values. -/
theorem conj_curv_eq_aux (S : Fields) (u v : ℝ) :
    starRingEnd ℂ (curv S u v) = (S.mu u v : ℂ) +
      (1 - S.mu u v) * S.xi u v * starRingEnd ℂ (S.theta u v) /
        ((S.nu u v : ℂ) * S.lam u v) := by
  simp only [curv, map_add, map_div₀, map_mul, map_sub, map_one, Complex.conj_ofReal,
    starRingEnd_self_apply]
  rw [mul_comm (S.lam u v : ℂ) (S.nu u v : ℂ)]
  ring

/-- [node restart-bv-C-u]
The incoming conjugate curvature primitive equation, charged_SF_new_version.tex:L4536–4538.
The covariant scalar derivatives cancel their connection contributions in the
curvature product. All coefficients and the Maxwell sign are exact. -/
theorem bv_c_u {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    HasDerivWithinAt (fun s => (S.r s v : ℂ) * starRingEnd ℂ (curv S s v))
      ((S.r u v : ℂ) * (starRingEnd ℂ (S.theta u v) / S.lam u v) *
        kC1 e (triangle 0 T) S u v +
        (S.nu u v * S.Q u v ^ 2 / S.r u v ^ 2 : ℝ) +
        I * e * S.Q u v * S.xi u v * starRingEnd ℂ (S.phi u v)) (Icc 0 v) u := by
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have he := hS.eq_u _ hp huv
  have hr := (hS.r_pos _ hp huv).ne'
  have hl := (hS.lam_pos _ hp).ne'
  have hn := (hS.nu_neg _ hp).ne
  have hm := (hS.one_sub_mu_pos _ hp).ne'
  have hrC : (S.r u v : ℂ) ≠ 0 := by exact_mod_cast hr
  have hlC : (S.lam u v : ℂ) ≠ 0 := by exact_mod_cast hl
  have hnC : (S.nu u v : ℂ) ≠ 0 := by exact_mod_cast hn
  have hmC : 1 - (S.mu u v : ℂ) ≠ 0 := by exact_mod_cast hm
  have dr := hasDerivWithinAt_u_aux hS.c1_r hu huv.le hvT
  have dl := hasDerivWithinAt_u_aux hS.c1_lam hu huv.le hvT
  have dn := hasDerivWithinAt_u_aux hS.c1_nu hu huv.le hvT
  have dt := hasDerivWithinAt_u_aux hS.c1_theta hu huv.le hvT
  have dx := hasDerivWithinAt_u_aux hS.c1_xi hu huv.le hvT
  have dm := hasDerivWithinAt_mu_u_aux hS hu huv hvT
  have dc := dm.ofReal_comp.add
    ((((dm.const_sub 1).ofReal_comp.mul dx).mul dt.star).div
      (dn.ofReal_comp.mul dl.ofReal_comp) (mul_ne_zero hnC hlC))
  have hd := dr.ofReal_comp.mul dc
  have hd' := hd.congr
    (f₁ := fun s => (S.r s v : ℂ) * starRingEnd ℂ (curv S s v))
    (fun s _ => by simp only [conj_curv_eq_aux, Pi.mul_apply, Pi.div_apply, Pi.add_apply,
      ofReal_sub, ofReal_one, ← starRingEnd_apply])
    (by simp only [conj_curv_eq_aux, Pi.mul_apply, Pi.div_apply, Pi.add_apply,
      ofReal_sub, ofReal_one, ← starRingEnd_apply])
  apply hd'.congr_deriv
  simp only [Pi.mul_apply, Pi.div_apply, Pi.add_apply]
  have ha := bv_c_u_algebra (S.r u v : ℂ) (S.lam u v : ℂ) (S.nu u v : ℂ)
    (S.mu u v : ℂ) (S.Q u v : ℂ) (I * e)
    (starRingEnd ℂ (S.theta u v)) (S.xi u v) (starRingEnd ℂ (S.xi u v))
    (starRingEnd ℂ (S.phi u v))
    (pdU (triangle 0 T) S.xi u v + I * e * S.A u v * S.xi u v)
    ((pdU (triangle 0 T) S.nu u v : ℝ) : ℂ) hrC hlC hnC hmC
  dsimp only at ha
  rw [kC1, pdU_b_eq_aux hS hu huv hvT, Fields.b]
  rw [he.1, he.2.1, he.2.2.1, he.2.2.2.2.1, he.2.2.2.2.2]
  dsimp only [Fields.mU, Fields.rUV, Fields.phiU, Fields.thetaU, Fields.waveSource]
  have hnorm : ‖S.xi u v / S.nu u v‖ ^ 2 = ‖S.xi u v‖ ^ 2 / S.nu u v ^ 2 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, div_pow, sq_abs]
  have hnormC : (‖S.xi u v / S.nu u v‖ : ℂ) ^ 2 =
      (‖S.xi u v‖ : ℂ) ^ 2 / (S.nu u v : ℂ) ^ 2 := by exact_mod_cast hnorm
  rw [hnormC]
  push_cast
  simp only [starRingEnd_apply, star_mul, star_div₀, star_neg, star_sub]
  simp only [← starRingEnd_apply, map_one, Complex.conj_ofReal, Complex.conj_I]
  simp only [← Complex.conj_mul']
  dsimp only [Fields.mu] at ha hmC ⊢
  push_cast at ha hmC ⊢
  have hdenC : (S.r u v : ℂ) - 2 * (S.m u v : ℂ) ≠ 0 := by
    intro hz
    apply hmC
    field_simp [hrC]
    linear_combination hz
  convert ha using 1 <;> field_simp [hrC, hlC, hnC, hmC, hdenC] <;> ring

end EmcsfAcExtension.Local
