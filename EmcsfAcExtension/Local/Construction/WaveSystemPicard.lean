module

public import EmcsfAcExtension.Local.Defs.Picard
import EmcsfAcExtension.Local.Construction.ReconBasic

/-! # Incoming derivatives recovered from the literal Picard updates

The first regularity step in internal project record `#smooth-regularity`, equations H3.
The coefficient continuity assumptions are kept separate from the fixed-point
equations. In particular neither incoming derivative is an input assumption.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Local.Recon

variable {e : ℝ} {lam : ℝ → ℝ → ℝ} {hh : ℝ → ℝ → ℂ}
  {c b u v : ℝ} {lam₀ : ℝ → ℝ} {h₀ : ℝ → ℂ}

/-- The logarithmic expansion Picard update has the incoming derivative
prescribed by its old continuous coefficient, including both endpoints as
within derivatives. There are no sign assumptions or estimate constants. -/
theorem hasDerivWithinAt_picardLam_of_continuous
    (hG : ContinuousOn (fun s => nu e lam hh s v / r lam s v * z e lam hh s v)
      (Icc c b)) (hu : u ∈ Icc c b) :
    HasDerivWithinAt (fun x => picardLam e lam hh c lam₀ x v)
      (picardLam e lam hh c lam₀ u v *
        (nu e lam hh u v / r lam u v * z e lam hh u v)) (Icc c b) u := by
  simpa only [picardLam, mul_assoc, mul_left_comm, mul_comm] using!
    ((hasDerivWithinAt_primitive hG hu).exp.const_mul (lam₀ v))

/-- An explicit expansion fixed-point equation recovers the incoming
expansion derivative. The only analytic input is continuity of the
reconstructed logarithmic coefficient on this incoming section. -/
theorem hasDerivWithinAt_lam_of_picardLam
    (hG : ContinuousOn (fun s => nu e lam hh s v / r lam s v * z e lam hh s v)
      (Icc c b)) (hu : u ∈ Icc c b)
    (hfix : ∀ x ∈ Icc c b, picardLam e lam hh c lam₀ x v = lam x v) :
    HasDerivWithinAt (fun x => lam x v)
      (lam u v * (nu e lam hh u v / r lam u v * z e lam hh u v)) (Icc c b) u := by
  have hd := hasDerivWithinAt_picardLam_of_continuous (lam₀ := lam₀) hG hu
  rw [hfix u hu] at hd
  exact hd.congr (fun x hx => (hfix x hx).symm) (hfix u hu).symm

private theorem unitary_update_factorization {A : ℝ → ℝ} {P : ℝ → ℂ}
    (hA : ContinuousOn A (Icc c b)) (hu : u ∈ Icc c b) (e : ℝ) (h : ℂ) :
    Complex.exp (-(I * e * ∫ s in c..u, A s)) * h +
        (∫ s in c..u, Complex.exp (-(I * e * ∫ t in s..u, A t)) * P s) =
      Complex.exp (-(I * e * ∫ s in c..u, A s)) *
        (h + ∫ s in c..u, Complex.exp (I * e * ∫ t in c..s, A t) * P s) := by
  have hi {x : ℝ} (hx : x ∈ Icc c b) : IntervalIntegrable A volume c x :=
    (hA.mono (Icc_subset_Icc le_rfl hx.2)).intervalIntegrable_of_Icc hx.1
  rw [mul_add, ← intervalIntegral.integral_const_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  dsimp only
  have hs' : s ∈ Icc c b := by
    rw [uIcc_of_le hu.1] at hs
    exact ⟨hs.1, hs.2.trans hu.2⟩
  have hadd := intervalIntegral.integral_interval_sub_left (hi hu) (hi hs')
  rw [← hadd, Complex.ofReal_sub]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- A unitary variation-of-constants update solves its incoming ordinary
linear equation on a closed section when its potential and forcing are
continuous. This elementary calculus lemma includes endpoint derivatives
and imposes no regularity assumption on the update itself. -/
theorem hasDerivWithinAt_unitary_update_of_continuous {A : ℝ → ℝ} {P : ℝ → ℂ}
    (hA : ContinuousOn A (Icc c b)) (hP : ContinuousOn P (Icc c b))
    (hu : u ∈ Icc c b) (e : ℝ) (h : ℂ) :
    let H := fun x => Complex.exp (-(I * e * ∫ s in c..x, A s)) * h +
      ∫ s in c..x, Complex.exp (-(I * e * ∫ t in s..x, A t)) * P s
    HasDerivWithinAt H (-(I * e * A u) * H u + P u) (Icc c b) u := by
  let p (x : ℝ) : ℂ := (∫ s in c..x, A s : ℝ)
  let w (x : ℝ) := Complex.exp (-(I * e * p x))
  let H (x : ℝ) := w x *
    (h + ∫ s in c..x, Complex.exp (I * e * p s) * P s)
  have cp : ContinuousOn p (Icc c b) :=
    Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_primitive (hu.1.trans hu.2)
        (hA.intervalIntegrable_of_Icc (hu.1.trans hu.2)))
  have dp : HasDerivWithinAt p (A u : ℂ) (Icc c b) u :=
    (hasDerivWithinAt_primitive hA hu).ofReal_comp
  have dw : HasDerivWithinAt w (w u * -(I * e * A u)) (Icc c b) u :=
    (dp.const_mul (I * e)).neg.cexp
  have cR : ContinuousOn (fun s => Complex.exp (I * e * p s) * P s) (Icc c b) :=
    (continuousOn_const.mul cp).cexp.mul hP
  have dH := dw.mul ((hasDerivWithinAt_primitive cR hu).const_add h)
  have hcancel : w u * Complex.exp (I * e * p u) = 1 := by
    dsimp only [w]
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  have hd : HasDerivWithinAt H (-(I * e * A u) * H u + P u) (Icc c b) u := by
    convert dH using 1
    dsimp only [H]
    linear_combination -P u * hcancel
  have heq : ∀ x ∈ Icc c b, H x =
      Complex.exp (-(I * e * ∫ s in c..x, A s)) * h +
        ∫ s in c..x, Complex.exp (-(I * e * ∫ t in s..x, A t)) * P s := by
    intro x hx
    exact (unitary_update_factorization hA hx e h).symm
  rw [heq u hu] at hd
  exact hd.congr (fun x hx => (heq x hx).symm) (heq u hu).symm

/-- The literal scalar Picard update solves its incoming ordinary transport
equation on any closed incoming section where its reconstructed potential
and forcing are continuous. Derivatives of the candidate are not inputs.
The connection multiplies the updated scalar, as in internal project record F1 and H3. -/
theorem hasDerivWithinAt_picardH_of_continuous
    (hA : ContinuousOn (fun s => A e lam hh s v) (Icc c b))
    (hP : ContinuousOn (fun s =>
      (((-nu e lam hh s v / r lam s v : ℝ) : ℂ) *
        ((z e lam hh s v : ℂ) * ratio lam hh s v +
          I * e * Q e lam hh s v * phi lam hh s v / (1 - (mu e lam hh s v : ℂ)))))
      (Icc c b)) (hu : u ∈ Icc c b) :
    HasDerivWithinAt (fun x => picardH e lam hh c h₀ x v)
      (-(I * e * A e lam hh u v) * picardH e lam hh c h₀ u v +
        (((-nu e lam hh u v / r lam u v : ℝ) : ℂ) *
          ((z e lam hh u v : ℂ) * ratio lam hh u v +
            I * e * Q e lam hh u v * phi lam hh u v / (1 - (mu e lam hh u v : ℂ)))))
      (Icc c b) u :=
  hasDerivWithinAt_unitary_update_of_continuous hA hP hu e (h₀ v)

/-- An explicit scalar fixed-point equation recovers its incoming derivative.
The two analytic premises concern the reconstructed potential and forcing;
the fixed-point equation is kept as a literal equality on the section. -/
theorem hasDerivWithinAt_h_of_picardH
    (hA : ContinuousOn (fun s => A e lam hh s v) (Icc c b))
    (hP : ContinuousOn (fun s =>
      (((-nu e lam hh s v / r lam s v : ℝ) : ℂ) *
        ((z e lam hh s v : ℂ) * ratio lam hh s v +
          I * e * Q e lam hh s v * phi lam hh s v / (1 - (mu e lam hh s v : ℂ)))))
      (Icc c b)) (hu : u ∈ Icc c b)
    (hfix : ∀ x ∈ Icc c b, picardH e lam hh c h₀ x v = hh x v) :
    HasDerivWithinAt (fun x => hh x v)
      (-(I * e * A e lam hh u v) * hh u v +
        (((-nu e lam hh u v / r lam u v : ℝ) : ℂ) *
          ((z e lam hh u v : ℂ) * ratio lam hh u v +
            I * e * Q e lam hh u v * phi lam hh u v / (1 - (mu e lam hh u v : ℂ)))))
      (Icc c b) u := by
  have hd := hasDerivWithinAt_picardH_of_continuous (h₀ := h₀) hA hP hu
  rw [hfix u hu] at hd
  exact hd.congr (fun x hx => (hfix x hx).symm) (hfix u hu).symm

/-- A Picard fixed point has its prescribed cone values. Both equalities are
evaluated at the initial endpoint, where the integrals vanish identically. -/
theorem cone_values_of_picard
    (hL : picardLam e lam hh c lam₀ c v = lam c v)
    (hH : picardH e lam hh c h₀ c v = hh c v) :
    lam c v = lam₀ v ∧ hh c v = h₀ v := by
  simpa [picardLam, picardH] using And.intro hL.symm hH.symm

end EmcsfAcExtension.Local.Recon
