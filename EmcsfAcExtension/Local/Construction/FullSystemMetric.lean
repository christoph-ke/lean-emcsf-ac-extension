module

public import EmcsfAcExtension.Local.Construction.FullSystemCarrier
public import EmcsfAcExtension.Frozen.Fields.Omega2
import EmcsfAcExtension.Local.Construction.FullSystemCoefficients
import EmcsfAcExtension.Local.Calculus.MixedIdentity
import EmcsfAcExtension.Local.Calculus.LogPartials
import EmcsfAcExtension.Local.Algebra.Raychaudhuri
import EmcsfAcExtension.Local.Algebra.Geometric

/-! # Metric completeness of the reconstructed C¹ system

internal project record (35)–(37), L692–L734. All selected second derivatives
are obtained from first-order primitives on closed off-axis rectangles.
The metric is the frozen `Fields.Omega2`; no metric equation is assumed.
-/

public section

open Set Complex

namespace EmcsfAcExtension.Local.Null

/-- Metric conclusions complementary to the thirteen reduced equations.
Closed off-axis rectangles retain all physical boundary points of a
construction wedge. The mixed metric derivative is an actual derivative
of the outgoing derivative of `log Ω²`, including rectangle endpoints.
This record is used only as a conclusion of recovery. -/
structure MetricIdentities (S : Fields) (D : Set (ℝ × ℝ)) : Prop where
  /-- Positivity of the literal metric coefficient, including the axis. -/
  omega_pos : ∀ p ∈ D, 0 < S.Omega2 p.1 p.2
  /-- The defining mass identity with nonzero positive metric coefficient. -/
  mass_identity : ∀ p ∈ D,
    1 - S.mu p.1 p.2 = -4 * S.nu p.1 p.2 * S.lam p.1 p.2 / S.Omega2 p.1 p.2
  /-- Raychaudhuri, the two logarithmic metric derivatives, the pure radius
  derivatives, and the mixed logarithmic identities (36)–(37). -/
  on_rectangle : ∀ {α β γ δ : ℝ}, α < β → γ < δ →
    Icc α β ×ˢ Icc γ δ ⊆ D ∩ {p : ℝ × ℝ | p.1 < p.2} →
    ∀ u ∈ Icc α β, ∀ v ∈ Icc γ δ,
    let r := S.r u v
    let l := S.lam u v
    let n := S.nu u v
    let d := 1 - S.mu u v
    let z := (S.mu u v - S.Q u v ^ 2 / r ^ 2) / d
    let Lu := pdU D S.nu u v / n + ‖S.xi u v‖ ^ 2 / (n * r)
    let Lv := pdV D S.lam u v / l + ‖S.theta u v‖ ^ 2 / (l * r)
    HasDerivWithinAt (fun x => Real.log (S.lam x v / (1 - S.mu x v)))
      (‖S.xi u v‖ ^ 2 / (n * r)) (Icc α β) u ∧
    HasDerivWithinAt (fun y => Real.log (-S.nu u y / (1 - S.mu u y)))
      (‖S.theta u v‖ ^ 2 / (l * r)) (Icc γ δ) v ∧
    HasDerivWithinAt (fun x => Real.log (S.Omega2 x v)) Lu (Icc α β) u ∧
    HasDerivWithinAt (fun y => Real.log (S.Omega2 u y)) Lv (Icc γ δ) v ∧
    HasDerivWithinAt (fun x => pdU D S.r x v) (pdU D S.nu u v) (Icc α β) u ∧
    HasDerivWithinAt (fun y => pdV D S.r u y) (pdV D S.lam u v) (Icc γ δ) v ∧
    pdU D S.nu u v - n * Lu = -‖S.xi u v‖ ^ 2 / r ∧
    pdV D S.lam u v - l * Lv = -‖S.theta u v‖ ^ 2 / r ∧
    HasDerivWithinAt (fun x => pdV D (fun s t => Real.log (S.lam s t)) x v)
      (n * l / r ^ 2 * ((1 + z) * ‖S.theta u v / l‖ ^ 2 - 2 * z +
        2 * S.Q u v ^ 2 / (d * r ^ 2) -
        2 * S.Q u v * pdV D S.Q u v / (d * l * r))) (Icc α β) u ∧
    HasDerivWithinAt
      (fun x => derivWithin (fun y => Real.log (S.Omega2 x y)) (Icc γ δ) v)
      (-2 * (starRingEnd ℂ (S.theta u v) * S.xi u v).re / r ^ 2 +
        S.Omega2 u v * S.mu u v / (2 * r ^ 2) -
        S.Omega2 u v * S.Q u v ^ 2 / r ^ 4) (Icc α β) u

private theorem pd_log {D : Set (ℝ × ℝ)} {f : ℝ → ℝ → ℝ}
    (hD : UniqueDiffOn ℝ D) (cf : ContDiffOn ℝ 1 (Function.uncurry f) D)
    {p : ℝ × ℝ} (hp : p ∈ D) (hn : f p.1 p.2 ≠ 0) (w : ℝ × ℝ) :
    fderivWithin ℝ (fun q => Real.log (f q.1 q.2)) D p w =
      fderivWithin ℝ (Function.uncurry f) D p w / f p.1 p.2 := by
  have hd := ((cf.differentiableOn (by norm_num) p hp).hasFDerivWithinAt.log hn).fderivWithin
    (hD p hp)
  change (fderivWithin ℝ (fun q : ℝ × ℝ => Real.log (f q.1 q.2)) D p) w = _
  simp only [Function.uncurry_def] at hd
  rw [hd]
  simp only [smul_apply, smul_eq_mul, div_eq_mul_inv, Function.uncurry_def]
  ring

private theorem gap_num_ne {r m : ℝ} (hr : r ≠ 0) (hgap : 1 - 2 * m / r ≠ 0) :
    r - 2 * m ≠ 0 := by
  intro hz
  apply hgap
  field_simp [hr]
  linear_combination hz

/-- Completeness of the reduced system in the C¹ class, internal project record
(35)–(37). The only analytic input is the reduced C¹ system and uniqueness
of the domain differential. Mixed derivatives are proved by differentiating
an incoming primitive, without C² or an extra metric premise. There are
no estimate constants. -/
theorem metric_identities_of_c1 {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hD : UniqueDiffOn ℝ D) (hS : IsC1Solution e S D) : MetricIdentities S D := by
  have hop (p : ℝ × ℝ) (hp : p ∈ D) : 0 < S.Omega2 p.1 p.2 := by
    exact div_pos (mul_pos (mul_pos_of_neg_of_neg (by norm_num) (hS.nu_neg p hp))
      (hS.lam_pos p hp)) (hS.one_sub_mu_pos p hp)
  refine ⟨hop, ?_, ?_⟩
  · intro p hp
    dsimp only [Fields.Omega2]
    field_simp [(hS.nu_neg p hp).ne, (hS.lam_pos p hp).ne',
      (hS.one_sub_mu_pos p hp).ne']
  intro α β γ δ hab hcd hrect u hu v hv
  let R := Icc α β ×ˢ Icc γ δ
  have hs : R ⊆ D := fun p hp => (hrect hp).1
  have hp : (u, v) ∈ D := hs ⟨hu, hv⟩
  have huv : u < v := (hrect (show (u, v) ∈ R from ⟨hu, hv⟩)).2
  have heU := hS.eq_u (u, v) hp huv
  have heV := hS.eq_v (u, v) hp huv
  have hr := (hS.r_pos (u, v) hp huv).ne'
  have hl := (hS.lam_pos (u, v) hp).ne'
  have hn := (hS.nu_neg (u, v) hp).ne
  have hh := (hS.one_sub_mu_pos (u, v) hp).ne'
  have hden := gap_num_ne hr hh
  have hruv : S.rUV u v = S.nu u v * S.lam u v / S.r u v *
      ((S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) / (1 - S.mu u v)) := by
    rfl
  have dU {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      {f : ℝ → ℝ → E} (cf : ContDiffOn ℝ 1 (Function.uncurry f) D) :
      HasDerivWithinAt (fun x => f x v) (pdU D f u v) (Icc α β) u :=
    hasDerivWithinAt_pdU cf hp (fun x hx => hs ⟨hx, hv⟩)
  have dV {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      {f : ℝ → ℝ → E} (cf : ContDiffOn ℝ 1 (Function.uncurry f) D) :
      HasDerivWithinAt (f u) (pdV D f u v) (Icc γ δ) v :=
    hasDerivWithinAt_pdV cf hp (fun y hy => hs ⟨hu, hy⟩)
  have dru := dU hS.c1_r
  have drv := dV hS.c1_r
  have dlu := dU hS.c1_lam
  have dnv := dV hS.c1_nu
  rw [heU.1] at dru
  rw [heV.1] at drv
  have dmu := (((dU hS.c1_m).const_mul 2).div dru hr)
  have dmv := (((dV hS.c1_m).const_mul 2).div drv hr)
  have rayU := (dlu.div (dmu.const_sub 1) hh).log (div_ne_zero hl hh)
  have rayV := (dnv.neg.div (dmv.const_sub 1) hh).log (div_ne_zero (neg_ne_zero.mpr hn) hh)
  have arU := eq_ray_in_algebra hr hl hn hh (heU.2.1.trans hruv) heU.2.2.1
  have arV := eq_ray_out_algebra hr hl hn hh (heV.2.1.trans hruv) heV.2.2.1
  have rayU' : HasDerivWithinAt (fun x => Real.log (S.lam x v / (1 - S.mu x v)))
      (‖S.xi u v‖ ^ 2 / (S.nu u v * S.r u v)) (Icc α β) u := by
    apply rayU.congr_deriv
    calc
      _ = pdU D S.lam u v / S.lam u v +
          (2 * pdU D S.m u v / S.r u v -
            2 * S.m u v * S.nu u v / S.r u v ^ 2) / (1 - S.mu u v) := by
        simp only [Pi.div_apply, Fields.mu]
        field_simp [hr, hl, hh, hden]
        ring
      _ = _ := arU
  have rayV' : HasDerivWithinAt (fun y => Real.log (-S.nu u y / (1 - S.mu u y)))
      (‖S.theta u v‖ ^ 2 / (S.lam u v * S.r u v)) (Icc γ δ) v := by
    apply rayV.congr_deriv
    calc
      _ = pdV D S.nu u v / S.nu u v +
          (2 * pdV D S.m u v / S.r u v -
            2 * S.m u v * S.lam u v / S.r u v ^ 2) / (1 - S.mu u v) := by
        simp only [Pi.div_apply, Pi.neg_apply, Fields.mu]
        field_simp [hr, hn, hh, hden]
        ring
      _ = _ := arV
  have omegaU : HasDerivWithinAt (fun x => Real.log (S.Omega2 x v))
      (pdU D S.nu u v / S.nu u v + ‖S.xi u v‖ ^ 2 / (S.nu u v * S.r u v))
      (Icc α β) u := by
    have h := (((dU hS.c1_nu).const_mul (-4)).log
      (mul_ne_zero (by norm_num) hn)).add rayU'
    apply h.congr_deriv (by field_simp [hn]) |>.congr
    · intro x hx
      have hpx : (x, v) ∈ D := hs ⟨hx, hv⟩
      simp only [Pi.add_apply]
      rw [← Real.log_mul
        (mul_ne_zero (by norm_num : (-4 : ℝ) ≠ 0) (hS.nu_neg (x, v) hpx).ne)
        (div_ne_zero (hS.lam_pos (x, v) hpx).ne'
          (hS.one_sub_mu_pos (x, v) hpx).ne')]
      congr 1; dsimp only [Fields.Omega2]; ring
    · simp only [Pi.add_apply]
      rw [← Real.log_mul (mul_ne_zero (by norm_num : (-4 : ℝ) ≠ 0) hn)
        (div_ne_zero hl hh)]
      congr 1; dsimp only [Fields.Omega2]; ring
  have omegaV (x : ℝ) (hx : x ∈ Icc α β) (y : ℝ) (hy : y ∈ Icc γ δ) :
      HasDerivWithinAt (fun t => Real.log (S.Omega2 x t))
        (pdV D S.lam x y / S.lam x y + ‖S.theta x y‖ ^ 2 / (S.lam x y * S.r x y))
        (Icc γ δ) y := by
    have hpx : (x, y) ∈ D := hs ⟨hx, hy⟩
    have hxy : x < y := (hrect (show (x, y) ∈ R from ⟨hx, hy⟩)).2
    have hrx := (hS.r_pos _ hpx hxy).ne'
    have hlx := (hS.lam_pos _ hpx).ne'
    have hnx := (hS.nu_neg _ hpx).ne
    have hhx := (hS.one_sub_mu_pos _ hpx).ne'
    have hdenx := gap_num_ne hrx hhx
    have dr := hasDerivWithinAt_pdV hS.c1_r hpx (fun t ht => hs ⟨hx, ht⟩)
    have dm := hasDerivWithinAt_pdV hS.c1_m hpx (fun t ht => hs ⟨hx, ht⟩)
    have dn := hasDerivWithinAt_pdV hS.c1_nu hpx (fun t ht => hs ⟨hx, ht⟩)
    have dl := hasDerivWithinAt_pdV hS.c1_lam hpx (fun t ht => hs ⟨hx, ht⟩)
    have dμ := (dm.const_mul 2).div dr hrx
    have h := ((dn.neg.div (dμ.const_sub 1) hhx).log
      (div_ne_zero (neg_ne_zero.mpr hnx) hhx))
    have ha := eq_ray_out_algebra hrx hlx hnx hhx
      (hS.eq_v _ hpx hxy).2.1 (hS.eq_v _ hpx hxy).2.2.1
    have hq : HasDerivWithinAt (fun t => Real.log (-S.nu x t / (1 - S.mu x t)))
        (‖S.theta x y‖ ^ 2 / (S.lam x y * S.r x y)) (Icc γ δ) y := by
      apply h.congr_deriv
      rw [(hS.eq_v _ hpx hxy).1]
      calc
        _ = pdV D S.nu x y / S.nu x y +
            (2 * pdV D S.m x y / S.r x y -
              2 * S.m x y * S.lam x y / S.r x y ^ 2) / (1 - S.mu x y) := by
          simp only [Pi.div_apply, Pi.neg_apply, Fields.mu]
          field_simp [hrx, hnx, hhx, hdenx]
          ring
        _ = _ := ha
    have hd := (dl.log hlx).add ((hasDerivWithinAt_const y (Icc γ δ) (4 : ℝ)).log
      (by norm_num) |>.add hq)
    apply (hd.congr_deriv (by simp only [zero_div, zero_add])).congr
    · intro t ht
      simp only [Pi.add_apply]
      have hpt : (x, t) ∈ D := hs ⟨hx, ht⟩
      have hnxt := (hS.nu_neg (x, t) hpt).ne
      have hlxt := (hS.lam_pos (x, t) hpt).ne'
      have hhxt := (hS.one_sub_mu_pos (x, t) hpt).ne'
      rw [← Real.log_mul (by norm_num : (4 : ℝ) ≠ 0)
        (div_ne_zero (neg_ne_zero.mpr hnxt) hhxt), ← Real.log_mul hlxt
          (mul_ne_zero (by norm_num) (div_ne_zero (neg_ne_zero.mpr hnxt) hhxt))]
      congr 1; dsimp only [Fields.Omega2]; ring
    · simp only [Pi.add_apply]
      rw [← Real.log_mul (by norm_num : (4 : ℝ) ≠ 0)
        (div_ne_zero (neg_ne_zero.mpr hnx) hhx), ← Real.log_mul hlx
          (mul_ne_zero (by norm_num) (div_ne_zero (neg_ne_zero.mpr hnx) hhx))]
      congr 1; dsimp only [Fields.Omega2]; ring
  let G (x y : ℝ) := S.nu x y / S.r x y *
    ((S.mu x y - S.Q x y ^ 2 / S.r x y ^ 2) / (1 - S.mu x y))
  have cμ : ContDiffOn ℝ 1 (Function.uncurry S.mu) R :=
    ((contDiffOn_const.mul (hS.c1_m.mono hs)).div (hS.c1_r.mono hs)
      (fun p hp => (hS.r_pos p (hs hp) (hrect hp).2).ne'))
  have cG : ContDiffOn ℝ 1 (Function.uncurry G) R :=
    ((hS.c1_nu.mono hs).div (hS.c1_r.mono hs)
      (fun p hp => (hS.r_pos p (hs hp) (hrect hp).2).ne')).mul
      ((cμ.sub (((hS.c1_Q.mono hs).pow 2).div ((hS.c1_r.mono hs).pow 2)
        (fun p hp => pow_ne_zero 2 (hS.r_pos p (hs hp) (hrect hp).2).ne'))).div
          (contDiffOn_const.sub cμ) (fun p hp => (hS.one_sub_mu_pos p (hs hp)).ne'))
  have cLog : ContDiffOn ℝ 1
      (Function.uncurry (fun x y => Real.log (S.lam x y))) D :=
    hS.c1_lam.log (fun p hp => (hS.lam_pos p hp).ne')
  have htrans (x : ℝ) (hx : x ∈ Icc α β) (y : ℝ) (hy : y ∈ Icc γ δ) :
      pdU D (fun s t => Real.log (S.lam s t)) x y = G x y := by
    have hpx : (x, y) ∈ D := hs ⟨hx, hy⟩
    change fderivWithin ℝ (fun p => Real.log (S.lam p.1 p.2)) D (x, y) (1, 0) = _
    rw [pd_log hD hS.c1_lam hpx (hS.lam_pos _ hpx).ne']
    change pdU D S.lam x y / S.lam x y = _
    rw [(hS.eq_u _ hpx (hrect ⟨hx, hy⟩).2).2.1]
    dsimp only [G, Fields.rUV]
    field_simp [(hS.lam_pos _ hpx).ne']
  have hR : UniqueDiffOn ℝ R := (uniqueDiffOn_Icc hab).prod (uniqueDiffOn_Icc hcd)
  have cJ := continuousOn_pdV cG hR
  have hswap : MapsTo (fun p : ℝ × ℝ => (p.2, p.1))
      (Icc γ δ ×ˢ Icc α β) R := fun p hp => ⟨hp.2, hp.1⟩
  have hmix := mixed_u_pdV_of_transport_aux
    (f := fun x y => Real.log (S.lam x y)) (G := G) (Gv := pdV R G) hab hcd hs cLog
    (cG.continuousOn.comp (continuousOn_snd.prodMk continuousOn_fst) hswap)
    (cJ.comp (continuousOn_snd.prodMk continuousOn_fst) hswap) htrans
    (fun y hy x hx => hasDerivWithinAt_pdV cG ⟨hx, hy⟩ (fun t ht => ⟨hx, ht⟩)) hu hv
  let Mv := 2 * pdV D S.m u v / S.r u v -
    2 * S.m u v * S.lam u v / S.r u v ^ 2
  let B := S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2
  let H := 1 - S.mu u v
  let Bv := Mv - 2 * S.Q u v * S.QV e u v / S.r u v ^ 2 +
    2 * S.Q u v ^ 2 * S.lam u v / S.r u v ^ 3
  let Lg := S.rUV u v / S.r u v * (B / H) -
    S.nu u v * S.lam u v / S.r u v ^ 2 * (B / H) +
    S.nu u v / S.r u v * (Bv / H + B * Mv / H ^ 2)
  have dqv := dV hS.c1_Q
  rw [heV.2.1] at dnv
  rw [heV.2.2.2.1] at dqv
  have dG := (dnv.div drv hr).mul
    ((dmv.sub ((dqv.pow 2).div (drv.pow 2) (pow_ne_zero 2 hr))).div (dmv.const_sub 1) hh)
  have dG' : HasDerivWithinAt (G u) Lg (Icc γ δ) v := by
    apply dG.congr_deriv
    dsimp only [Lg, Bv, Mv, B, H, Fields.mu]
    simp only [Pi.div_apply, Pi.pow_apply, Pi.sub_apply]
    field_simp [hr, hh, hden]
    ring
  have hjet := (uniqueDiffOn_Icc hcd v hv).eq_deriv _
    (hasDerivWithinAt_pdV cG ⟨hu, hv⟩ (fun t ht => ⟨hu, ht⟩)) dG'
  rw [hjet] at hmix
  have dt := dU hS.c1_theta
  let thetaDu := pdU D S.theta u v + I * e * S.A u v * S.theta u v
  have hconn : (starRingEnd ℂ (S.theta u v) *
      (I * e * S.A u v * S.theta u v)).re = 0 := by
    have heq : starRingEnd ℂ (S.theta u v) * (I * e * S.A u v * S.theta u v) =
        I * e * S.A u v * (starRingEnd ℂ (S.theta u v) * S.theta u v) := by ring
    rw [heq, Complex.conj_mul']
    simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, zero_add, add_zero, sub_zero]
  have dnorm : HasDerivWithinAt (fun x => ‖S.theta x v‖ ^ 2)
      (2 * (starRingEnd ℂ (S.theta u v) * thetaDu).re) (Icc α β) u := by
    apply (hasDerivWithinAt_norm_sq_complex_aux dt).congr_deriv
    simp only [thetaDu, mul_add, Complex.add_re, hconn, add_zero]
  let Qg := 2 * (starRingEnd ℂ (S.theta u v) * thetaDu).re /
      (S.lam u v * S.r u v) -
    ‖S.theta u v‖ ^ 2 * (S.rUV u v * S.r u v + S.lam u v * S.nu u v) /
      (S.lam u v * S.r u v) ^ 2
  rw [heU.2.1] at dlu
  have dquad : HasDerivWithinAt
      (fun x => ‖S.theta x v‖ ^ 2 / (S.lam x v * S.r x v)) Qg (Icc α β) u := by
    apply (dnorm.div (dlu.mul dru) (mul_ne_zero hl hr)).congr_deriv
    dsimp only [Qg]
    simp only [Pi.mul_apply]
    field_simp [hl, hr]
  have hvlog (x : ℝ) (hx : x ∈ Icc α β) :
      pdV D (fun s t => Real.log (S.lam s t)) x v = pdV D S.lam x v / S.lam x v :=
    pd_log hD hS.c1_lam (hs ⟨hx, hv⟩) (hS.lam_pos _ (hs ⟨hx, hv⟩)).ne' (0, 1)
  have hd := (hmix.add dquad).congr
    (fun x hx => ((omegaV x hx v hv).derivWithin (uniqueDiffOn_Icc hcd v hv)).trans
      (by simp only [Pi.add_apply]; rw [hvlog x hx]))
    (((omegaV u hu v hv).derivWithin (uniqueDiffOn_Icc hcd v hv)).trans
      (by simp only [Pi.add_apply]; rw [hvlog u hu]))
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
    (lamU := S.rUV u v) (nuV := S.rUV u v) (mV := pdV D S.m u v)
    (muV := Mv) (QV := S.QV e u v)
    hr hl hn hh rfl rfl heV.2.2.1 rfl rfl hthetaDu
  have hd' : HasDerivWithinAt
      (fun x => derivWithin (fun y => Real.log (S.Omega2 x y)) (Icc γ δ) v)
      (-2 * (starRingEnd ℂ (S.theta u v) * S.xi u v).re / S.r u v ^ 2 +
        S.Omega2 u v * S.mu u v / (2 * S.r u v ^ 2) -
        S.Omega2 u v * S.Q u v ^ 2 / S.r u v ^ 4) (Icc α β) u := by
    apply hd.congr_deriv
    change Lg + Qg = _
    change Lg + Qg = _ at ha
    rw [ha]
    simp only [Fields.Omega2, Fields.mu, Complex.add_re, Complex.div_ofReal_re,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
      Complex.conj_re, Complex.conj_im]
    field_simp [hr, hl, hn, hh, hden]
    ring
  have hmV' : Mv = S.lam u v / S.r u v *
      ((1 - S.mu u v) * ‖S.theta u v / S.lam u v‖ ^ 2 +
        S.Q u v ^ 2 / S.r u v ^ 2 - S.mu u v) := by
    dsimp only [Mv]
    rw [heV.2.2.1]
    dsimp only [Fields.mV, Fields.mu]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, div_pow, sq_abs]
    field_simp [hr, hl]
  have h36 := geom_log_mixed_algebra (QD := S.QV e u v) hr hl hh hruv hmV'
  have h36' : HasDerivWithinAt (fun x => pdV D (fun s t => Real.log (S.lam s t)) x v)
      (S.nu u v * S.lam u v / S.r u v ^ 2 *
        ((1 + B / H) * ‖S.theta u v / S.lam u v‖ ^ 2 - 2 * (B / H) +
          2 * S.Q u v ^ 2 / (H * S.r u v ^ 2) -
          2 * S.Q u v * pdV D S.Q u v / (H * S.lam u v * S.r u v))) (Icc α β) u := by
    apply hmix.congr_deriv
    simpa only [Lg, Bv, B, H, heV.2.2.2.1] using
      h36
  refine ⟨rayU', rayV', omegaU, omegaV u hu v hv, ?_, ?_, ?_, ?_, h36', hd'⟩
  · exact (dU hS.c1_nu).congr
      (fun x hx => (hS.eq_u (x, v) (hs ⟨hx, hv⟩)
        (hrect (show (x, v) ∈ R from ⟨hx, hv⟩)).2).1)
      heU.1
  · exact (dV hS.c1_lam).congr
      (fun y hy => (hS.eq_v (u, y) (hs ⟨hu, hy⟩)
        (hrect (show (u, y) ∈ R from ⟨hu, hy⟩)).2).1)
      heV.1
  · field_simp [hn, hr]
    ring
  · field_simp [hl, hr]
    ring

/-- [node restart-sec-independent-null-construction#smooth-full-system]
Complete C¹-route export of the full EMCSF system from the original raw
carrier. Besides all thirteen reduced equations and the regular zero axis
gauge, the frozen metric coefficient satisfies the Raychaudhuri and mixed
metric equations (35)–(37). No extra regularity or metric premise is used.
The fixed positive bounds `l,κ` precede the candidate; there are no
estimate constants. -/
theorem smooth_full_system_metric
    {a b c l κ e : ℝ} {lam lamV : ℝ → ℝ → ℝ} {hh hhV : ℝ → ℝ → ℂ}
    {lam₀ : ℝ → ℝ} {h₀ : ℝ → ℂ} (hac : a < c) (hcb : c ≤ b)
    (hl : 0 < l) (hκ : 0 < κ)
    (_cLam₀ : ContDiffOn ℝ 1 lam₀ (Icc a b))
    (_cH₀ : ContDiffOn ℝ 1 h₀ (Icc a b))
    (cl : ContinuousOn (Function.uncurry lam) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (ch : ContinuousOn (Function.uncurry hh) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (clV : ContinuousOn (Function.uncurry lamV) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (chV : ContinuousOn (Function.uncurry hhV) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (fl : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      lam p.1 p.2 = lam p.1 p.1 + ∫ s in p.1..p.2, lamV p.1 s)
    (fh : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      hh p.1 p.2 = hh p.1 p.1 + ∫ s in p.1..p.2, hhV p.1 s)
    (cG : ContinuousOn (fun p : ℝ × ℝ => Recon.nu e lam hh p.1 p.2 /
      Recon.r lam p.1 p.2 * Recon.z e lam hh p.1 p.2)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (cA : ContinuousOn (Function.uncurry (Recon.A e lam hh))
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (cP : ContinuousOn (fun p : ℝ × ℝ =>
      (((-Recon.nu e lam hh p.1 p.2 / Recon.r lam p.1 p.2 : ℝ) : ℂ) *
        ((Recon.z e lam hh p.1 p.2 : ℂ) * Recon.ratio lam hh p.1 p.2 +
          I * e * Recon.Q e lam hh p.1 p.2 * Recon.phi lam hh p.1 p.2 /
            (1 - (Recon.mu e lam hh p.1 p.2 : ℂ)))))
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (hL : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      Recon.picardLam e lam hh a lam₀ p.1 p.2 = lam p.1 p.2)
    (hH : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      Recon.picardH e lam hh a h₀ p.1 p.2 = hh p.1 p.2)
    (hlo : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}, l ≤ lam p.1 p.2)
    (hgap : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      κ ≤ 1 - Recon.mu e lam hh p.1 p.2) :
    let D := triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}
    let S := Recon.toFields e lam hh
    IsC1Solution e S D ∧ (∀ t ∈ Icc a c, S.A t t = 0) ∧
      ContDiffOn ℝ 1 (Function.uncurry S.Omega2) D ∧ MetricIdentities S D := by
  obtain ⟨hS, hA⟩ := smooth_full_system hac hcb hl hκ _cLam₀ _cH₀
    cl ch clV chV fl fh cG cA cP hL hH hlo hgap
  obtain ⟨cl1, ch1⟩ := contDiffOn_pair_of_picard_carrier hac hcb cl ch clV chV fl fh cG cA cP hL hH
  obtain ⟨_, _, cμ, _, _, _, _, _⟩ :=
    contDiffOn_reconstruction_coefficients hac hcb hl hκ cl1 ch1 hlo hgap
  have cΩ : ContDiffOn ℝ 1 (Function.uncurry (Recon.toFields e lam hh).Omega2)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) :=
    (((contDiffOn_const (c := (-4 : ℝ))).mul hS.c1_nu).mul hS.c1_lam).div
      (contDiffOn_const.sub cμ) (fun p hp => (hκ.trans_le (hgap p hp)).ne')
  exact ⟨hS, hA, cΩ, metric_identities_of_c1
    (uniqueDiffOn_triangle_inter_fst_le hac hcb) hS⟩

end EmcsfAcExtension.Local.Null
