module

public import EmcsfAcExtension.Local.Apriori.SmoothSupJetFields
import EmcsfAcExtension.Local.Calculus.Raychaudhuri
import EmcsfAcExtension.Local.Calculus.OffAxisMixed
import EmcsfAcExtension.Local.Calculus.TransportRegularity

/-! # The geometric transport coefficient and its regular first-jet formula

Both derivatives are expressed as polynomials in the same regular inputs used
for the field jets. In particular no derivative of a singular quotient is left
as an uncontrolled input.
-/

public section

open Set Complex

namespace EmcsfAcExtension.Local

/-- The incoming logarithmic expansion coefficient `G` of charged_SF_new_version.tex:L6290.
Division is totalized on the axis, where its value is zero. -/
@[expose] noncomputable def smoothGeomCoeff (S : Fields) (u v : ℝ) : ℝ :=
  S.nu u v / S.r u v *
    ((S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) / (1 - S.mu u v))

/-- A regular directional derivative formula for `G`. Here `q=Q/r³`,
`m=μ/r²`, `fSq` is the squared normalized scalar derivative, and `qx=∂Q`.
All inverses are explicit inputs; the formula is polynomial in its inputs. -/
@[expose] noncomputable def smoothGeomPartial (r n d di q m nx rx fSq qx : ℝ) : ℝ :=
  let b := m - q ^ 2 * r ^ 2
  let a := rx * (d * fSq + q ^ 2 * r ^ 2 - m)
  nx * r * b * di + n * (a - 2 * q * qx + 2 * q ^ 2 * r ^ 2 * rx) * di +
    n * r ^ 2 * b * a * di ^ 2 - n * b * rx * di

/-- The value, incoming derivative and outgoing derivative of `G`, in that
order, as continuous formulas on the fixed numerical jet input space.
The two Maxwell signs are retained separately. -/
@[expose] noncomputable def smoothGeomJetFormula (e : ℝ)
    (x : (Fin 15 → ℝ) × (Fin 5 → ℂ)) : Fin 3 → ℝ :=
  let r := x.1 0
  let l := x.1 1
  let n := x.1 2
  let d := x.1 3
  let q := x.1 4
  let m := x.1 5
  let di := x.1 14
  ![n * r * (m - q ^ 2 * r ^ 2) * di,
    smoothGeomPartial r n d di q m (x.1 9) n (‖x.2 2‖ ^ 2)
      (e * n * r ^ 2 * (starRingEnd ℂ (x.2 0) * x.2 2).im),
    smoothGeomPartial r n d di q m (x.1 10) l (‖x.2 1‖ ^ 2)
      (-(e * l * r ^ 2 * (starRingEnd ℂ (x.2 0) * x.2 1).im))]

/-- The regular geometric jet formula is continuous everywhere on its
numerical input space. This assertion selects no estimate constant. -/
theorem continuous_smoothGeomJetFormula (e : ℝ) : Continuous (smoothGeomJetFormula e) := by
  apply continuous_pi
  intro i
  fin_cases i <;> dsimp only [smoothGeomJetFormula, smoothGeomPartial,
    Matrix.cons_val_zero, Matrix.cons_val_succ] <;> fun_prop

/-- `G` is C¹ on the off-axis part of a classical triangle, including its
initial and terminal edges. No second derivatives are used. -/
theorem smooth_geom_coeff_c1_off_aux {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) :
    ContDiffOn ℝ 1 (Function.uncurry (smoothGeomCoeff S))
      {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ T} := by
  let O := {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ T}
  have hs : O ⊆ triangle 0 T := fun p hp => ⟨hp.1, hp.2.1.le, hp.2.2⟩
  have cr := hS.c1_r.mono hs
  have cq := hS.c1_Q.mono hs
  have cm := c1_mu_off_aux hS
  have hr (p : ℝ × ℝ) (hp : p ∈ O) : S.r p.1 p.2 ≠ 0 :=
    (hS.r_pos p (hs hp) hp.2.1).ne'
  exact ((hS.c1_nu.mono hs).div cr hr).mul
    ((cm.sub ((cq.pow 2).div (cr.pow 2) (fun p hp => pow_ne_zero 2 (hr p hp)))).div
      ((contDiffOn_const (c := (1 : ℝ))).sub cm)
      (fun p hp => (hS.one_sub_mu_pos p (hs hp)).ne'))

private theorem geom_partial_algebra {r n m q rx nx mx qx fSq : ℝ}
    (hr : r ≠ 0) (_hd : 1 - 2 * m / r ≠ 0)
    (hm : mx = rx / 2 * ((1 - 2 * m / r) * r ^ 2 * fSq + q ^ 2 / r ^ 2)) :
    (nx / r - n * rx / r ^ 2) *
        ((2 * m / r - q ^ 2 / r ^ 2) / (1 - 2 * m / r)) +
      n / r *
        (((2 * mx / r - 2 * m * rx / r ^ 2) -
            (2 * q * qx / r ^ 2 - 2 * q ^ 2 * rx / r ^ 3)) / (1 - 2 * m / r) +
          (2 * m / r - q ^ 2 / r ^ 2) *
            (2 * mx / r - 2 * m * rx / r ^ 2) / (1 - 2 * m / r) ^ 2) =
      smoothGeomPartial r n (1 - 2 * m / r) (1 - 2 * m / r)⁻¹
        (q / r ^ 3) (2 * m / r / r ^ 2) nx rx fSq qx := by
  rw [hm]
  dsimp only [smoothGeomPartial]
  field_simp [hr, _hd]
  ring

private theorem geom_deriv {s : Set ℝ} {x : ℝ} {r n m q : ℝ → ℝ}
    {rx nx mx qx : ℝ} (dr : HasDerivWithinAt r rx s x)
    (dn : HasDerivWithinAt n nx s x) (dm : HasDerivWithinAt m mx s x)
    (dq : HasDerivWithinAt q qx s x) (hr : r x ≠ 0)
    (hd : 1 - 2 * m x / r x ≠ 0) :
    HasDerivWithinAt
      (fun t => n t / r t * ((2 * m t / r t - q t ^ 2 / r t ^ 2) /
        (1 - 2 * m t / r t)))
      ((nx / r x - n x * rx / r x ^ 2) *
          ((2 * m x / r x - q x ^ 2 / r x ^ 2) / (1 - 2 * m x / r x)) +
        n x / r x *
          (((2 * mx / r x - 2 * m x * rx / r x ^ 2) -
              (2 * q x * qx / r x ^ 2 - 2 * q x ^ 2 * rx / r x ^ 3)) /
              (1 - 2 * m x / r x) +
            (2 * m x / r x - q x ^ 2 / r x ^ 2) *
              (2 * mx / r x - 2 * m x * rx / r x ^ 2) /
              (1 - 2 * m x / r x) ^ 2)) s x := by
  have dmu := (dm.const_mul 2).div dr hr
  apply ((dn.div dr hr).mul
    ((dmu.sub ((dq.pow 2).div (dr.pow 2) (pow_ne_zero 2 hr))).div
      (dmu.const_sub 1) hd)).congr_deriv
  simp only [Pi.div_apply, Pi.pow_apply, Pi.sub_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  field_simp [hr, hd]
  ring

/-- The incoming derivative of `G` equals its regular numerical formula
on every off-axis section, including boundary points. There are no estimate
constants or additional derivative hypotheses. -/
theorem smooth_geom_coeff_deriv_u_aux {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    HasDerivWithinAt (fun x => smoothGeomCoeff S x v)
      (smoothGeomJetFormula e (smoothJetInput e T S u v) 1) (Icc 0 v) u := by
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have hr := (hS.r_pos _ hp huv).ne'
  have hx := (hS.nu_neg _ hp).ne
  have hd := (hS.one_sub_mu_pos _ hp).ne'
  have he := hS.eq_u _ hp huv
  have dr : HasDerivWithinAt (fun x => S.r x v) (S.nu u v) (Icc 0 v) u := by
    simpa only [he.1] using hasDerivWithinAt_u_aux hS.c1_r hu huv.le hvT
  have dn := hasDerivWithinAt_u_aux hS.c1_nu hu huv.le hvT
  have dm : HasDerivWithinAt (fun x => S.m x v) (S.mU u v) (Icc 0 v) u := by
    simpa only [he.2.2.1] using hasDerivWithinAt_u_aux hS.c1_m hu huv.le hvT
  have dq : HasDerivWithinAt (fun x => S.Q x v) (S.QU e u v) (Icc 0 v) u := by
    simpa only [he.2.2.2.1] using hasDerivWithinAt_u_aux hS.c1_Q hu huv.le hvT
  have hm : S.mU u v = S.nu u v / 2 *
      ((1 - S.mu u v) * S.r u v ^ 2 *
        ‖S.xi u v / S.nu u v / S.r u v‖ ^ 2 + S.Q u v ^ 2 / S.r u v ^ 2) := by
    simp only [Fields.mU, norm_div, Complex.norm_real, Real.norm_eq_abs,
      div_pow, sq_abs]
    field_simp [hr, hx]
  have hq : S.QU e u v = (e * S.nu u v * S.r u v ^ 2 *
        (starRingEnd ℂ (S.phi u v) * (S.xi u v / S.nu u v / S.r u v)).im) := by
    simp only [Fields.QU, ← mul_div_assoc, Complex.div_ofReal_im]
    field_simp [hr, hx]
  apply (geom_deriv dr dn dm dq hr hd).congr_deriv
  change _ = smoothGeomPartial (S.r u v) (S.nu u v) (1 - S.mu u v)
    (1 - S.mu u v)⁻¹ (S.Q u v / S.r u v ^ 3) (S.mu u v / S.r u v ^ 2)
    (pdU (triangle 0 T) S.nu u v) (S.nu u v)
    (‖S.xi u v / S.nu u v / S.r u v‖ ^ 2) _
  dsimp [smoothJetInput]
  rw [← hq]
  exact geom_partial_algebra hr hd hm

/-- The outgoing derivative of `G` equals its regular numerical formula
on every off-axis section, including boundary points. There are no estimate
constants or additional derivative hypotheses. -/
theorem smooth_geom_coeff_deriv_v_aux {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    HasDerivWithinAt (smoothGeomCoeff S u)
      (smoothGeomJetFormula e (smoothJetInput e T S u v) 2) (Icc u T) v := by
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have hr := (hS.r_pos _ hp huv).ne'
  have hx := (hS.lam_pos _ hp).ne'
  have hd := (hS.one_sub_mu_pos _ hp).ne'
  have he := hS.eq_v _ hp huv
  have dr : HasDerivWithinAt (S.r u) (S.lam u v) (Icc u T) v := by
    simpa only [he.1] using hasDerivWithinAt_v_aux hS.c1_r hu huv.le hvT
  have dn := hasDerivWithinAt_v_aux hS.c1_nu hu huv.le hvT
  have dm : HasDerivWithinAt (S.m u) (S.mV u v) (Icc u T) v := by
    simpa only [he.2.2.1] using hasDerivWithinAt_v_aux hS.c1_m hu huv.le hvT
  have dq : HasDerivWithinAt (S.Q u) (S.QV e u v) (Icc u T) v := by
    simpa only [he.2.2.2.1] using hasDerivWithinAt_v_aux hS.c1_Q hu huv.le hvT
  have hm : S.mV u v = S.lam u v / 2 *
      ((1 - S.mu u v) * S.r u v ^ 2 *
        ‖S.theta u v / S.lam u v / S.r u v‖ ^ 2 + S.Q u v ^ 2 / S.r u v ^ 2) := by
    simp only [Fields.mV, norm_div, Complex.norm_real, Real.norm_eq_abs,
      div_pow, sq_abs]
    field_simp [hr, hx]
  have hq : S.QV e u v = -(e * S.lam u v * S.r u v ^ 2 *
        (starRingEnd ℂ (S.phi u v) * (S.theta u v / S.lam u v / S.r u v)).im) := by
    simp only [Fields.QV, ← mul_div_assoc, Complex.div_ofReal_im]
    field_simp [hr, hx]
  apply (geom_deriv dr dn dm dq hr hd).congr_deriv
  change _ = smoothGeomPartial (S.r u v) (S.nu u v) (1 - S.mu u v)
    (1 - S.mu u v)⁻¹ (S.Q u v / S.r u v ^ 3) (S.mu u v / S.r u v ^ 2)
    (pdV (triangle 0 T) S.nu u v) (S.lam u v)
    (‖S.theta u v / S.lam u v / S.r u v‖ ^ 2) _
  dsimp [smoothJetInput]
  rw [← hq]
  exact geom_partial_algebra hr hd hm

end EmcsfAcExtension.Local
