module

public import EmcsfAcExtension.Local.Calculus.Raychaudhuri
public import EmcsfAcExtension.Local.Defs.Renormalized
import EmcsfAcExtension.Local.Calculus.LogPartials
import EmcsfAcExtension.Local.Calculus.TransportRegularity
import EmcsfAcExtension.Local.Calculus.OffAxisMixed
import EmcsfAcExtension.Local.Algebra.Geometric

/-! # The common geometric transport source on the classical class

The mixed logarithmic derivatives are recovered from characteristic integral
representations. The remaining quadratic derivatives use the real norm-square
chain rule; the algebraic core performs the Maxwell cancellation.
-/

public section

open Set Complex

namespace EmcsfAcExtension.Local

/-- The outgoing geometric renormalization as the outgoing logarithmic partial
plus the quadratic correction. The identity includes the axis with total division. -/
theorem geomL_as_log_partial_aux {e T : ℝ} {S : Fields} (hT : 0 < T)
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ} (hp : (u, v) ∈ triangle 0 T) :
    geomL (triangle 0 T) S u v =
      pdV (triangle 0 T) (fun x y => Real.log (S.lam x y)) u v +
        ‖S.theta u v‖ ^ 2 / (S.lam u v * S.r u v) := by
  rw [geomL, pdV_log_aux hT hS.c1_lam hp (hS.lam_pos _ hp).ne']
  congr 1
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, div_pow, sq_abs]
  by_cases hr : S.r u v = 0
  · simp only [hr, div_zero, mul_zero, zero_mul]
  · field_simp [hr, (hS.lam_pos _ hp).ne']

/-- [node restart-bv-geom-trans]
Incoming transport of the outgoing geometric renormalization, with the exact
common source of charged_SF_new_version.tex:L4850–4855. The integral route justifies the mixed
partial on the C¹ class without a C² premise. -/
theorem bv_geom_trans_out {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    HasDerivWithinAt (fun x => geomL (triangle 0 T) S x v)
      (geomSource S u v) (Icc 0 v) u := by
  have hT : 0 < T := hu.trans_lt (huv.trans_le hvT)
  let O := {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ T}
  have hs : O ⊆ triangle 0 T := fun p hp => ⟨hp.1, hp.2.1.le, hp.2.2⟩
  let G (x y : ℝ) := S.nu x y / S.r x y *
    ((S.mu x y - S.Q x y ^ 2 / S.r x y ^ 2) / (1 - S.mu x y))
  have cG : ContDiffOn ℝ 1 (Function.uncurry G) O := by
    have cr := hS.c1_r.mono hs
    have cq := hS.c1_Q.mono hs
    have cm := c1_mu_off_aux hS
    have hr (p : ℝ × ℝ) (hp : p ∈ O) : S.r p.1 p.2 ≠ 0 :=
      (hS.r_pos p (hs hp) hp.2.1).ne'
    exact ((hS.c1_nu.mono hs).div cr hr).mul
      ((cm.sub ((cq.pow 2).div (cr.pow 2) (fun p hp => pow_ne_zero 2 (hr p hp)))).div
        ((contDiffOn_const (c := (1 : ℝ))).sub cm)
        (fun p hp => (hS.one_sub_mu_pos p (hs hp)).ne'))
  have cf : ContDiffOn ℝ 1
      (Function.uncurry (fun x y => Real.log (S.lam x y))) (triangle 0 T) := by
    simpa only [Function.uncurry_def] using
      hS.c1_lam.log (fun p hp => (hS.lam_pos p hp).ne')
  have htrans (x y : ℝ) (hx : 0 ≤ x) (hxy : x < y) (hy : y ≤ T) :
      pdU (triangle 0 T) (fun a b => Real.log (S.lam a b)) x y = G x y := by
    have hp : (x, y) ∈ triangle 0 T := ⟨hx, hxy.le, hy⟩
    rw [pdU_log_aux hT hS.c1_lam hp (hS.lam_pos _ hp).ne', (hS.eq_u _ hp hxy).2.1]
    dsimp only [G, Fields.rUV]
    field_simp [(hS.lam_pos _ hp).ne']
  have hmix := mixed_u_pdV_triangle_of_c1_transport_aux
    (f := fun x y => Real.log (S.lam x y)) (G := G) cf cG htrans hu huv hvT
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have heV := hS.eq_v _ hp huv
  have heU := hS.eq_u _ hp huv
  have hr := (hS.r_pos _ hp huv).ne'
  have hl := (hS.lam_pos _ hp).ne'
  have hn := (hS.nu_neg _ hp).ne
  have hh := (hS.one_sub_mu_pos _ hp).ne'
  let Mv := 2 * pdV (triangle 0 T) S.m u v / S.r u v -
    2 * S.m u v * S.lam u v / S.r u v ^ 2
  let B := S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2
  let H := 1 - S.mu u v
  let Bv := Mv - 2 * S.Q u v * S.QV e u v / S.r u v ^ 2 +
    2 * S.Q u v ^ 2 * S.lam u v / S.r u v ^ 3
  let Lg := S.rUV u v / S.r u v * (B / H) -
    S.nu u v * S.lam u v / S.r u v ^ 2 * (B / H) +
    S.nu u v / S.r u v * (Bv / H + B * Mv / H ^ 2)
  have drv : HasDerivWithinAt (S.r u) (S.lam u v) (Icc u T) v := by
    simpa only [heV.1] using hasDerivWithinAt_v_aux hS.c1_r hu huv.le hvT
  have dnv : HasDerivWithinAt (S.nu u) (S.rUV u v) (Icc u T) v := by
    simpa only [heV.2.1] using hasDerivWithinAt_v_aux hS.c1_nu hu huv.le hvT
  have dqv : HasDerivWithinAt (S.Q u) (S.QV e u v) (Icc u T) v := by
    simpa only [heV.2.2.2.1] using hasDerivWithinAt_v_aux hS.c1_Q hu huv.le hvT
  have dmv := hasDerivWithinAt_mu_v_aux hS hu huv hvT
  have dB := dmv.sub ((dqv.pow 2).div (drv.pow 2) (pow_ne_zero 2 hr))
  have dG := (dnv.div drv hr).mul (dB.div (dmv.const_sub 1) hh)
  have dG' : HasDerivWithinAt (G u) Lg (Icc u T) v := by
    apply dG.congr_deriv
    dsimp only [Lg, Bv, Mv, B, H]
    simp only [Pi.div_apply, Pi.pow_apply, Pi.sub_apply]
    field_simp [hr, hh]
    ring
  have hjet := (uniqueDiffOn_Icc (huv.trans_le hvT) v ⟨huv.le, hvT⟩).eq_deriv _
    (hasDerivWithinAt_off_triangle_v_aux cG hu huv hvT) dG'
  rw [hjet] at hmix
  have dru : HasDerivWithinAt (fun x => S.r x v) (S.nu u v) (Icc 0 v) u := by
    simpa only [heU.1] using hasDerivWithinAt_u_aux hS.c1_r hu huv.le hvT
  have dlu : HasDerivWithinAt (fun x => S.lam x v) (S.rUV u v) (Icc 0 v) u := by
    simpa only [heU.2.1] using hasDerivWithinAt_u_aux hS.c1_lam hu huv.le hvT
  have dt := hasDerivWithinAt_u_aux hS.c1_theta hu huv.le hvT
  let thetaDu := pdU (triangle 0 T) S.theta u v + I * e * S.A u v * S.theta u v
  have hconn : (starRingEnd ℂ (S.theta u v) *
      (I * e * S.A u v * S.theta u v)).re = 0 := by
    have heq : starRingEnd ℂ (S.theta u v) * (I * e * S.A u v * S.theta u v) =
        I * e * S.A u v * (starRingEnd ℂ (S.theta u v) * S.theta u v) := by ring
    rw [heq, Complex.conj_mul']
    simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, zero_add, add_zero, sub_zero]
  have dnorm : HasDerivWithinAt (fun x => ‖S.theta x v‖ ^ 2)
      (2 * (starRingEnd ℂ (S.theta u v) * thetaDu).re) (Icc 0 v) u := by
    apply (hasDerivWithinAt_norm_sq_complex_aux dt).congr_deriv
    simp only [thetaDu, mul_add, Complex.add_re, hconn, add_zero]
  let Qg := 2 * (starRingEnd ℂ (S.theta u v) * thetaDu).re /
      (S.lam u v * S.r u v) -
    ‖S.theta u v‖ ^ 2 * (S.rUV u v * S.r u v + S.lam u v * S.nu u v) /
      (S.lam u v * S.r u v) ^ 2
  have dquad : HasDerivWithinAt
      (fun x => ‖S.theta x v‖ ^ 2 / (S.lam x v * S.r x v)) Qg (Icc 0 v) u := by
    apply (dnorm.div (dlu.mul dru) (mul_ne_zero hl hr)).congr_deriv
    dsimp only [Qg]
    simp only [Pi.mul_apply]
    field_simp [hl, hr]
  have hd := (hmix.add dquad).congr
    (fun x hx => geomL_as_log_partial_aux hT hS ⟨hx.1, hx.2, hvT⟩)
    (geomL_as_log_partial_aux hT hS hp)
  apply hd.congr_deriv
  have hthetaDu : thetaDu = -(S.lam u v * S.xi u v / S.r u v) -
      I * e * S.Q u v * S.phi u v * S.nu u v * S.lam u v /
        ((1 - 2 * S.m u v / S.r u v) * S.r u v) := by
    dsimp only [thetaDu]
    rw [heU.2.2.2.2.2]
    dsimp only [Fields.thetaU, Fields.waveSource, Fields.mu]
    push_cast
    ring
  have ha := bv_geom_trans_out_algebra (r := S.r u v) (lam := S.lam u v)
    (nu := S.nu u v) (m := S.m u v) (Q := S.Q u v) (e := e)
    (lamU := S.rUV u v) (nuV := S.rUV u v) (mV := pdV (triangle 0 T) S.m u v)
    (muV := Mv) (QV := S.QV e u v)
    hr hl hn hh rfl rfl heV.2.2.1 rfl rfl hthetaDu
  simpa only [Lg, Qg, Bv, B, H, geomSource, curv, Fields.mu, ofReal_mul] using ha

/-- The incoming geometric renormalization as a logarithmic partial plus its
quadratic correction. Real logarithms satisfy `log ν = log (-ν)`, so the proof
uses `log ν` directly and retains the source's positive optical interpretation. -/
theorem geomN_as_log_partial_aux {e T : ℝ} {S : Fields} (hT : 0 < T)
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ} (hp : (u, v) ∈ triangle 0 T) :
    geomN (triangle 0 T) S u v =
      pdU (triangle 0 T) (fun x y => Real.log (S.nu x y)) u v +
        ‖S.xi u v‖ ^ 2 / (S.nu u v * S.r u v) := by
  rw [geomN, pdU_log_aux hT hS.c1_nu hp (hS.nu_neg _ hp).ne]
  congr 1
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, div_pow, sq_abs]
  by_cases hr : S.r u v = 0
  · simp only [hr, div_zero, mul_zero, zero_mul]
  · field_simp [hr, (hS.nu_neg _ hp).ne]

/-- [node restart-bv-geom-trans]
Outgoing transport of the incoming geometric renormalization, with exactly the
same common source. The mixed derivative again comes from the integral equation;
the incoming orientation and Maxwell sign are checked by its own algebraic core. -/
theorem bv_geom_trans_in {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    HasDerivWithinAt (fun y => geomN (triangle 0 T) S u y)
      (geomSource S u v) (Icc u T) v := by
  have hT : 0 < T := hu.trans_lt (huv.trans_le hvT)
  let O := {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ T}
  have hs : O ⊆ triangle 0 T := fun p hp => ⟨hp.1, hp.2.1.le, hp.2.2⟩
  let G (x y : ℝ) := S.lam x y / S.r x y *
    ((S.mu x y - S.Q x y ^ 2 / S.r x y ^ 2) / (1 - S.mu x y))
  have cG : ContDiffOn ℝ 1 (Function.uncurry G) O := by
    have cr := hS.c1_r.mono hs
    have cq := hS.c1_Q.mono hs
    have cm := c1_mu_off_aux hS
    have hr (p : ℝ × ℝ) (hp : p ∈ O) : S.r p.1 p.2 ≠ 0 :=
      (hS.r_pos p (hs hp) hp.2.1).ne'
    exact ((hS.c1_lam.mono hs).div cr hr).mul
      ((cm.sub ((cq.pow 2).div (cr.pow 2) (fun p hp => pow_ne_zero 2 (hr p hp)))).div
        ((contDiffOn_const (c := (1 : ℝ))).sub cm)
        (fun p hp => (hS.one_sub_mu_pos p (hs hp)).ne'))
  have cf : ContDiffOn ℝ 1
      (Function.uncurry (fun x y => Real.log (S.nu x y))) (triangle 0 T) := by
    simpa only [Function.uncurry_def] using
      hS.c1_nu.log (fun p hp => (hS.nu_neg p hp).ne)
  have htrans (x y : ℝ) (hx : 0 ≤ x) (hxy : x < y) (hy : y ≤ T) :
      pdV (triangle 0 T) (fun a b => Real.log (S.nu a b)) x y = G x y := by
    have hp : (x, y) ∈ triangle 0 T := ⟨hx, hxy.le, hy⟩
    rw [pdV_log_aux hT hS.c1_nu hp (hS.nu_neg _ hp).ne, (hS.eq_v _ hp hxy).2.1]
    dsimp only [G, Fields.rUV]
    field_simp [(hS.nu_neg _ hp).ne]
  have hmix := mixed_v_pdU_triangle_of_c1_transport_aux
    (f := fun x y => Real.log (S.nu x y)) (G := G) cf cG htrans hu huv hvT
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have heV := hS.eq_v _ hp huv
  have heU := hS.eq_u _ hp huv
  have hr := (hS.r_pos _ hp huv).ne'
  have hl := (hS.lam_pos _ hp).ne'
  have hn := (hS.nu_neg _ hp).ne
  have hh := (hS.one_sub_mu_pos _ hp).ne'
  let Mu := 2 * pdU (triangle 0 T) S.m u v / S.r u v -
    2 * S.m u v * S.nu u v / S.r u v ^ 2
  let B := S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2
  let H := 1 - S.mu u v
  let Bu := Mu - 2 * S.Q u v * S.QU e u v / S.r u v ^ 2 +
    2 * S.Q u v ^ 2 * S.nu u v / S.r u v ^ 3
  let Ng := S.rUV u v / S.r u v * (B / H) -
    S.lam u v * S.nu u v / S.r u v ^ 2 * (B / H) +
    S.lam u v / S.r u v * (Bu / H + B * Mu / H ^ 2)
  have dru : HasDerivWithinAt (fun x => S.r x v) (S.nu u v) (Icc 0 v) u := by
    simpa only [heU.1] using hasDerivWithinAt_u_aux hS.c1_r hu huv.le hvT
  have dlu : HasDerivWithinAt (fun x => S.lam x v) (S.rUV u v) (Icc 0 v) u := by
    simpa only [heU.2.1] using hasDerivWithinAt_u_aux hS.c1_lam hu huv.le hvT
  have dqu : HasDerivWithinAt (fun x => S.Q x v) (S.QU e u v) (Icc 0 v) u := by
    simpa only [heU.2.2.2.1] using hasDerivWithinAt_u_aux hS.c1_Q hu huv.le hvT
  have dmu := hasDerivWithinAt_mu_u_aux hS hu huv hvT
  have dB := dmu.sub ((dqu.pow 2).div (dru.pow 2) (pow_ne_zero 2 hr))
  have dG := (dlu.div dru hr).mul (dB.div (dmu.const_sub 1) hh)
  have dG' : HasDerivWithinAt (fun x => G x v) Ng (Icc 0 v) u := by
    apply dG.congr_deriv
    dsimp only [Ng, Bu, Mu, B, H]
    simp only [Pi.div_apply, Pi.pow_apply, Pi.sub_apply]
    field_simp [hr, hh]
    ring
  have hjet := (uniqueDiffOn_Icc (hu.trans_lt huv) u ⟨hu, huv.le⟩).eq_deriv _
    (hasDerivWithinAt_off_triangle_u_aux cG hu huv hvT) dG'
  rw [hjet] at hmix
  have drv : HasDerivWithinAt (S.r u) (S.lam u v) (Icc u T) v := by
    simpa only [heV.1] using hasDerivWithinAt_v_aux hS.c1_r hu huv.le hvT
  have dnv : HasDerivWithinAt (S.nu u) (S.rUV u v) (Icc u T) v := by
    simpa only [heV.2.1] using hasDerivWithinAt_v_aux hS.c1_nu hu huv.le hvT
  have dx : HasDerivWithinAt (S.xi u) (S.xiV e u v) (Icc u T) v := by
    simpa only [heV.2.2.2.2.2.2] using hasDerivWithinAt_v_aux hS.c1_xi hu huv.le hvT
  have dnorm := hasDerivWithinAt_norm_sq_complex_aux dx
  let Qg := 2 * (starRingEnd ℂ (S.xi u v) * S.xiV e u v).re /
      (S.nu u v * S.r u v) -
    ‖S.xi u v‖ ^ 2 * (S.rUV u v * S.r u v + S.nu u v * S.lam u v) /
      (S.nu u v * S.r u v) ^ 2
  have dquad : HasDerivWithinAt
      (fun y => ‖S.xi u y‖ ^ 2 / (S.nu u y * S.r u y)) Qg (Icc u T) v := by
    apply (dnorm.div (dnv.mul drv) (mul_ne_zero hn hr)).congr_deriv
    dsimp only [Qg]
    simp only [Pi.mul_apply]
    field_simp [hn, hr]
  have hd := (hmix.add dquad).congr
    (fun y hy => geomN_as_log_partial_aux hT hS ⟨hu, hy.1, hy.2⟩)
    (geomN_as_log_partial_aux hT hS hp)
  apply hd.congr_deriv
  have hruv : S.rUV u v = S.lam u v * S.nu u v / S.r u v *
      ((2 * S.m u v / S.r u v - S.Q u v ^ 2 / S.r u v ^ 2) /
        (1 - 2 * S.m u v / S.r u v)) := by
    dsimp only [Fields.rUV, Fields.mu]
    ring
  have hxiV : S.xiV e u v = -(S.nu u v * S.theta u v / S.r u v) +
      I * e * S.Q u v * S.phi u v * S.lam u v * S.nu u v /
        ((1 - 2 * S.m u v / S.r u v) * S.r u v) := by
    dsimp only [Fields.xiV, Fields.waveSource, Fields.mu]
    push_cast
    ring
  have ha := bv_geom_trans_in_algebra (r := S.r u v) (lam := S.lam u v)
    (nu := S.nu u v) (m := S.m u v) (Q := S.Q u v) (e := e)
    (lamU := S.rUV u v) (nuV := S.rUV u v) (mU := pdU (triangle 0 T) S.m u v)
    (muU := Mu) (QU := S.QU e u v)
    hr hl hn hh hruv hruv heU.2.2.1 rfl rfl hxiV
  simpa only [Ng, Qg, Bu, B, H, geomSource, curv, Fields.mu, ofReal_mul] using ha

end EmcsfAcExtension.Local
