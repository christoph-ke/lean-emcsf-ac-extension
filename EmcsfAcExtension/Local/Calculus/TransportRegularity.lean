module

public import EmcsfAcExtension.Local.Calculus.Normalized

/-! # Off-axis C¹ regularity of the prescribed transport sources

The scalar transport right sides use only C¹ fields and nonvanishing geometric
denominators. This supplies the source regularity for the integral mixed-partial route.
-/

public section

open Set Complex

namespace EmcsfAcExtension.Local

/-- The literal mass ratio is C¹ off the axis. No regularity of its singular
quotient formula at the axis is asserted. -/
theorem c1_mu_off_aux {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) :
    ContDiffOn ℝ 1 (Function.uncurry S.mu)
      {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ T} := by
  have hs : {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ T} ⊆ triangle 0 T :=
    fun p hp => ⟨hp.1, hp.2.1.le, hp.2.2⟩
  exact (((contDiffOn_const (c := (2 : ℝ))).mul (hS.c1_m.mono hs)).div (hS.c1_r.mono hs)
    (fun p hp => (hS.r_pos p (hs hp) hp.2.1).ne'))

/-- Incoming normalized transport source in a factored form, C¹ off the axis.
This is exactly the paper's source with a common denominator extracted. -/
theorem c1_normalized_source_in_aux {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ =>
      -(I * e * S.A p.1 p.2 * S.a p.1 p.2) +
        ((-S.nu p.1 p.2 / (S.r p.1 p.2 * (1 - S.mu p.1 p.2)) : ℝ) : ℂ) *
          (((S.mu p.1 p.2 - S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2 : ℝ) : ℂ) *
            (S.theta p.1 p.2 / S.lam p.1 p.2) + I * e * S.Q p.1 p.2 * S.phi p.1 p.2))
      {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ T} := by
  let O := {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ T}
  have hs : O ⊆ triangle 0 T := fun p hp => ⟨hp.1, hp.2.1.le, hp.2.2⟩
  have cr := hS.c1_r.mono hs
  have cl := hS.c1_lam.mono hs
  have cn := hS.c1_nu.mono hs
  have cq := hS.c1_Q.mono hs
  have cm := c1_mu_off_aux hS
  have hr (p : ℝ × ℝ) (hp : p ∈ O) : S.r p.1 p.2 ≠ 0 :=
    (hS.r_pos p (hs hp) hp.2.1).ne'
  have hh (p : ℝ × ℝ) (hp : p ∈ O) : 1 - S.mu p.1 p.2 ≠ 0 :=
    (hS.one_sub_mu_pos p (hs hp)).ne'
  have cH := (contDiffOn_const (c := (1 : ℝ))).sub cm
  have cC := cn.neg.div (cr.mul cH) (fun p hp => mul_ne_zero (hr p hp) (hh p hp))
  have cB := cm.sub ((cq.pow 2).div (cr.pow 2) (fun p hp => pow_ne_zero 2 (hr p hp)))
  have cL : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => (S.lam p.1 p.2 : ℂ)) O :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn cl
  have cY := (hS.c1_theta.mono hs).mul
    (cL.inv (fun p hp => Complex.ofReal_ne_zero.mpr (hS.lam_pos p (hs hp)).ne'))
  have cA : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => (S.A p.1 p.2 : ℂ)) O :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (hS.c1_A.mono hs)
  have cQ : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => (S.Q p.1 p.2 : ℂ)) O :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn cq
  simpa only [Fields.a, Function.uncurry_def, Pi.inv_apply, Pi.mul_apply, Function.comp_apply,
    ofRealCLM_apply, div_eq_mul_inv] using
    ((((contDiffOn_const (c := I * e)).mul cA).mul ((c1_a_aux hS).mono hs)).neg.add
      ((Complex.ofRealCLM.contDiff.comp_contDiffOn cC).mul
        (((Complex.ofRealCLM.contDiff.comp_contDiffOn cB).mul cY).add
          (((contDiffOn_const (c := I * e)).mul cQ).mul (hS.c1_phi.mono hs)))))

/-- Outgoing normalized transport source, C¹ off the axis. Its only denominators
are `r`, `ν` and `1-μ`, which have the class's strict signs. -/
theorem c1_normalized_source_out_aux {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ =>
      ((-S.lam p.1 p.2 / (S.r p.1 p.2 * (1 - S.mu p.1 p.2)) : ℝ) : ℂ) *
        (((S.mu p.1 p.2 - S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2 : ℝ) : ℂ) *
          (S.xi p.1 p.2 / S.nu p.1 p.2) - I * e * S.Q p.1 p.2 * S.phi p.1 p.2))
      {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ T} := by
  let O := {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ T}
  have hs : O ⊆ triangle 0 T := fun p hp => ⟨hp.1, hp.2.1.le, hp.2.2⟩
  have cr := hS.c1_r.mono hs
  have cl := hS.c1_lam.mono hs
  have cn := hS.c1_nu.mono hs
  have cq := hS.c1_Q.mono hs
  have cm := c1_mu_off_aux hS
  have hr (p : ℝ × ℝ) (hp : p ∈ O) : S.r p.1 p.2 ≠ 0 :=
    (hS.r_pos p (hs hp) hp.2.1).ne'
  have hh (p : ℝ × ℝ) (hp : p ∈ O) : 1 - S.mu p.1 p.2 ≠ 0 :=
    (hS.one_sub_mu_pos p (hs hp)).ne'
  have cH := (contDiffOn_const (c := (1 : ℝ))).sub cm
  have cC := cl.neg.div (cr.mul cH) (fun p hp => mul_ne_zero (hr p hp) (hh p hp))
  have cB := cm.sub ((cq.pow 2).div (cr.pow 2) (fun p hp => pow_ne_zero 2 (hr p hp)))
  have cN : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => (S.nu p.1 p.2 : ℂ)) O :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn cn
  have cZ := (hS.c1_xi.mono hs).mul
    (cN.inv (fun p hp => Complex.ofReal_ne_zero.mpr (hS.nu_neg p (hs hp)).ne))
  have cQ : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => (S.Q p.1 p.2 : ℂ)) O :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn cq
  simpa only [Function.uncurry_def, Pi.inv_apply, Pi.mul_apply, Function.comp_apply,
    ofRealCLM_apply, div_eq_mul_inv] using
    ((Complex.ofRealCLM.contDiff.comp_contDiffOn cC).mul
      (((Complex.ofRealCLM.contDiff.comp_contDiffOn cB).mul cZ).sub
        (((contDiffOn_const (c := I * e)).mul cQ).mul (hS.c1_phi.mono hs))))

end EmcsfAcExtension.Local
