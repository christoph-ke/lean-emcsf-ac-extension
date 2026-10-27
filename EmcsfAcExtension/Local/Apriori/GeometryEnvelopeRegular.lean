module

public import EmcsfAcExtension.Local.Defs.C1Class
public import EmcsfAcExtension.Local.Defs.Renormalized
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity
import EmcsfAcExtension.Local.Calculus.Partials
import EmcsfAcExtension.Infra.Calculus.TriangleDiff
import EmcsfAcExtension.Infra.Calculus.PartialsC1

/-! # Continuity of the classical geometric renormalizations

The scalar constraints replace the quadratic radius quotients by regular
expressions, including the literal zero axis values. No uniform bound on
classical derivative norms is assumed.
-/

public section

open Set Complex

namespace EmcsfAcExtension.Local

private theorem quadratic_radius_identity {r a : ℝ} {z : ℂ} (ha : a ≠ 0) :
    a / r * ‖(r : ℂ) * z / a‖ ^ 2 = r / a * ‖z‖ ^ 2 := by
  simp only [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    div_pow, mul_pow, sq_abs]
  by_cases hr : r = 0
  · simp [hr]
  · field_simp

/-- The outgoing geometric renormalization is continuous on the entire
classical triangle. No estimate constant or bound on higher derivatives
is needed; the quadratic correction vanishes continuously at the axis. -/
theorem continuousOn_geomL {e T : ℝ} {S : Fields} (hT : 0 < T)
    (hS : IsC1Solution e S (triangle 0 T)) :
    ContinuousOn (Function.uncurry (geomL (triangle 0 T) S)) (triangle 0 T) := by
  have cp := continuousOn_pdV hS.c1_phi (uniqueDiffOn_triangle hT)
  have cl := hS.c1_lam.continuousOn
  have cd := continuousOn_pdV hS.c1_lam (uniqueDiffOn_triangle hT)
  have cr := hS.c1_r.continuousOn
  have hl (p : ℝ × ℝ) (hp : p ∈ triangle 0 T) := (hS.lam_pos p hp).ne'
  have ce := (cd.div cl hl).add ((cr.div cl hl).mul (cp.norm.pow 2))
  apply ce.congr
  rintro ⟨u, v⟩ hp
  dsimp only [Function.uncurry_def, Pi.add_apply, Pi.div_apply, Pi.mul_apply,
    Pi.pow_apply, Function.comp_def]
  rw [geomL, theta_eq_radius_partial_aux hT hS hp, quadratic_radius_identity (hl (u, v) hp)]

/-- The incoming geometric renormalization is continuous up to the entire
regular axis in every real gauge. This is a qualitative classical fact,
with no estimate constant and no higher derivative norm premise. -/
theorem continuousOn_geomN {e T : ℝ} {S : Fields} (hT : 0 < T)
    (hS : IsC1Solution e S (triangle 0 T)) :
    ContinuousOn (Function.uncurry (geomN (triangle 0 T) S)) (triangle 0 T) := by
  have cp := continuousOn_pdU hS.c1_phi (uniqueDiffOn_triangle hT)
  have ca := (continuousOn_const (c := I * e)).mul
    (Complex.continuous_ofReal.comp_continuousOn hS.c1_A.continuousOn)
  have cq := cp.add (ca.mul hS.c1_phi.continuousOn)
  have cn := hS.c1_nu.continuousOn
  have cd := continuousOn_pdU hS.c1_nu (uniqueDiffOn_triangle hT)
  have cr := hS.c1_r.continuousOn
  have hn (p : ℝ × ℝ) (hp : p ∈ triangle 0 T) := (hS.nu_neg p hp).ne
  have ce := (cd.div cn hn).add ((cr.div cn hn).mul (cq.norm.pow 2))
  apply ce.congr
  rintro ⟨u, v⟩ hp
  dsimp only [Function.uncurry_def, Pi.add_apply, Pi.div_apply, Pi.mul_apply,
    Pi.pow_apply, Function.comp_def]
  rw [geomN, xi_eq_radius_covariant_partial_aux hT hS hp,
    quadratic_radius_identity (hn (u, v) hp)]

/-- The common geometric transport source is continuous off the axis.
There are no smallness or derivative-bound hypotheses. -/
theorem continuousOn_geomSource_off_axis {e T : ℝ} {S : Fields} (hT : 0 < T)
    (hS : IsC1Solution e S (triangle 0 T)) :
    ContinuousOn (Function.uncurry (geomSource S))
      (triangle 0 T ∩ {p : ℝ × ℝ | p.1 < p.2}) := by
  let O := triangle 0 T ∩ {p : ℝ × ℝ | p.1 < p.2}
  have cr := hS.c1_r.continuousOn.mono (inter_subset_left (t := {p | p.1 < p.2}))
  have cn := hS.c1_nu.continuousOn.mono (inter_subset_left (t := {p | p.1 < p.2}))
  have cl := hS.c1_lam.continuousOn.mono (inter_subset_left (t := {p | p.1 < p.2}))
  have cq := hS.c1_Q.continuousOn.mono (inter_subset_left (t := {p | p.1 < p.2}))
  have cm := (continuousOn_mu_aux hT hS).mono
    (inter_subset_left (t := {p : ℝ × ℝ | p.1 < p.2}))
  have cc := (continuousOn_curv_aux hT hS).mono
    (inter_subset_left (t := {p : ℝ × ℝ | p.1 < p.2}))
  have hr (p : ℝ × ℝ) (hp : p ∈ O) := (hS.r_pos p hp.1 hp.2).ne'
  have hH (p : ℝ × ℝ) (hp : p ∈ O) := (hS.one_sub_mu_pos p hp.1).ne'
  exact (((cn.const_mul 2).mul cl).div
    ((continuousOn_const.sub cm).mul (cr.pow 2))
      (fun p hp => mul_ne_zero (hH p hp) (pow_ne_zero 2 (hr p hp)))).neg.mul
        ((Complex.continuous_re.comp_continuousOn cc).sub
          (((cq.pow 2).div (cr.pow 2) (fun p hp => pow_ne_zero 2 (hr p hp))).const_mul 2))

end EmcsfAcExtension.Local
