module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Calculus.OffAxisMixed
import EmcsfAcExtension.Local.Calculus.TransportRegularity
import EmcsfAcExtension.Local.Calculus.Raychaudhuri
import EmcsfAcExtension.Local.Calculus.Partials
import EmcsfAcExtension.Local.Calculus.AxisRates
import EmcsfAcExtension.Local.Calculus.AxisRatio
import EmcsfAcExtension.Local.Calculus.AxisContinuity
import EmcsfAcExtension.Infra.Calculus.DiagonalChain

/-! # The missing incoming potential derivative

The mixed derivative is recovered from the outgoing potential constraint
by the landed integral representation theorem. No second derivative of
the solution is assumed. The quotient rule is kept factored for estimates.
-/

public section

open Set

namespace EmcsfAcExtension.Local

/-- The outgoing derivative of the incoming potential partial is the
incoming derivative of its constraint source. The literal quotient-rule
formula is valid on the classical C¹ class, by the integral mixed-partial
route. It contains no estimate constant or additional identity premise. -/
theorem smooth_potential_mixed_aux {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    let μu := 2 * pdU (triangle 0 T) S.m u v / S.r u v -
      2 * S.m u v * S.nu u v / S.r u v ^ 2
    let N := 2 * S.nu u v * S.lam u v * S.Q u v
    let Nu := 2 * (pdU (triangle 0 T) S.nu u v * S.lam u v +
      S.nu u v * pdU (triangle 0 T) S.lam u v) * S.Q u v +
        2 * S.nu u v * S.lam u v * S.QU e u v
    let d := (1 - S.mu u v) * S.r u v ^ 2
    let du := -μu * S.r u v ^ 2 + (1 - S.mu u v) * (2 * S.r u v * S.nu u v)
    HasDerivWithinAt (fun y => pdU (triangle 0 T) S.A u y)
      (Nu / d - N * du / d ^ 2) (Icc u T) v := by
  dsimp only
  let O := {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ T}
  have hsub : O ⊆ triangle 0 T := fun p hp => ⟨hp.1, hp.2.1.le, hp.2.2⟩
  have hAV : ContDiffOn ℝ 1 (Function.uncurry S.AV) O := by
    have cn := hS.c1_nu.mono hsub
    have cl := hS.c1_lam.mono hsub
    have cq := hS.c1_Q.mono hsub
    have cr := hS.c1_r.mono hsub
    have cm := c1_mu_off_aux hS
    exact ((((contDiffOn_const (c := (2 : ℝ))).mul cn).mul cl).mul cq).div
      (((contDiffOn_const (c := (1 : ℝ))).sub cm).mul (cr.pow 2))
      (fun p hp => mul_ne_zero (hS.one_sub_mu_pos _ (hsub hp)).ne'
        (pow_ne_zero 2 (hS.r_pos _ (hsub hp) hp.2.1).ne'))
  have hmix := mixed_v_pdU_triangle_of_c1_transport_aux hS.c1_A hAV
    (fun x y hx hxy hy => (hS.eq_v (x, y) ⟨hx, hxy.le, hy⟩ hxy).2.2.2.2.1)
    hu huv hvT
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have hr := (hS.r_pos _ hp huv).ne'
  have hd := (hS.one_sub_mu_pos _ hp).ne'
  have dr : HasDerivWithinAt (fun x => S.r x v) (S.nu u v) (Icc 0 v) u := by
    simpa only [(hS.eq_u _ hp huv).1] using hasDerivWithinAt_u_aux hS.c1_r hu huv.le hvT
  have dn := hasDerivWithinAt_u_aux hS.c1_nu hu huv.le hvT
  have dl := hasDerivWithinAt_u_aux hS.c1_lam hu huv.le hvT
  have dq : HasDerivWithinAt (fun x => S.Q x v) (S.QU e u v) (Icc 0 v) u := by
    simpa only [(hS.eq_u _ hp huv).2.2.2.1] using
      hasDerivWithinAt_u_aux hS.c1_Q hu huv.le hvT
  have dm := hasDerivWithinAt_mu_u_aux hS hu huv hvT
  have dAV := (((dn.const_mul 2).mul dl).mul dq).div
    ((dm.const_sub 1).mul (dr.pow 2)) (mul_ne_zero hd (pow_ne_zero 2 hr))
  have dAV' : HasDerivWithinAt (fun x => S.AV x v)
      ((2 * (pdU (triangle 0 T) S.nu u v * S.lam u v +
          S.nu u v * pdU (triangle 0 T) S.lam u v) * S.Q u v +
          2 * S.nu u v * S.lam u v * S.QU e u v) /
        ((1 - S.mu u v) * S.r u v ^ 2) -
        (2 * S.nu u v * S.lam u v * S.Q u v) *
          (-(2 * pdU (triangle 0 T) S.m u v / S.r u v -
              2 * S.m u v * S.nu u v / S.r u v ^ 2) * S.r u v ^ 2 +
            (1 - S.mu u v) * (2 * S.r u v * S.nu u v)) /
          ((1 - S.mu u v) * S.r u v ^ 2) ^ 2) (Icc 0 v) u := by
    apply dAV.congr_deriv
    simp only [Pi.mul_apply, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
    field_simp [hr, hd]
  have dAVoff := hasDerivWithinAt_off_triangle_u_aux hAV hu huv hvT
  have he := (uniqueDiffOn_Icc (hu.trans_lt huv) u ⟨hu, huv.le⟩).eq_deriv _ dAVoff dAV'
  rw [he] at hmix
  exact hmix

/-- Both ordinary potential partials vanish on the regular axis in the
restart gauge. Cubic charge gives the zero outgoing limit; the gauge's
diagonal derivative then gives the incoming limit. There are no size,
smallness or higher derivative assumptions. -/
theorem smooth_potential_axis_partials_aux {e T : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hT : 0 < T) (hS : IsC1Solution e S (triangle 0 T))
    (hdata : IsRestartData S h T) {t : ℝ} (ht : t ∈ Icc 0 T) :
    pdU (triangle 0 T) S.A t t = 0 ∧ pdV (triangle 0 T) S.A t t = 0 := by
  obtain ⟨q, cq, hq, hqa⟩ := exists_continuous_charge_square_ratio_aux hT hS
  have cm := continuousOn_mu_aux hT hS
  let F : ℝ × ℝ → ℝ := fun p =>
    2 * S.nu p.1 p.2 * S.lam p.1 p.2 * q p / (1 - S.mu p.1 p.2)
  have cF : ContinuousOn F (triangle 0 T) :=
    ((((hS.c1_nu.continuousOn.const_mul 2).mul hS.c1_lam.continuousOn).mul cq).div
      (continuousOn_const.sub cm) (fun p hp => (hS.one_sub_mu_pos p hp).ne'))
  have hV := eqOn_triangle_of_off_axis_aux hT
    (continuousOn_pdV hS.c1_A (uniqueDiffOn_triangle hT)) cF (by
      intro p hp huv
      change pdV (triangle 0 T) S.A p.1 p.2 = F p
      rw [(hS.eq_v p hp huv).2.2.2.2.1]
      dsimp only [Fields.AV, F]
      rw [hq p.1 p.2 hp huv]
      field_simp [(hS.r_pos p hp huv).ne', (hS.one_sub_mu_pos p hp).ne'])
  have hp : (t, t) ∈ triangle 0 T := ⟨ht.1, le_rfl, ht.2⟩
  have hv : pdV (triangle 0 T) S.A t t = 0 := by
    have hh := hV hp
    simpa only [Function.uncurry_def, F, hqa t ht, mul_zero, zero_div] using hh
  have hd := hasDerivWithinAt_diagonal hS.c1_A ht
  have hz : HasDerivWithinAt (fun x => S.A x x) 0 (Icc 0 T) t :=
    (hasDerivAt_const t (0 : ℝ)).hasDerivWithinAt.congr_of_mem hdata.2 ht
  have he := (uniqueDiffOn_Icc hT t ht).eq_deriv _ hd hz
  change pdU (triangle 0 T) S.A t t + pdV (triangle 0 T) S.A t t = 0 at he
  rw [hv, add_zero] at he
  exact ⟨he, hv⟩

end EmcsfAcExtension.Local
