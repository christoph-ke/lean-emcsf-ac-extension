module

public import EmcsfAcExtension.Local.Construction.ContinuationInputs
import EmcsfAcExtension.Local.Calculus.Partials

/-! # The enlarged C¹ cone class

Only the primary first jets and the positive expansion enter the
quotient estimate for `h = φ + θ/λ`. The enlarged bound is fixed before
the cone position and its distance from the old apex.
-/

public section

open Set

namespace EmcsfAcExtension.Local

private theorem continuation_cone_partial_bound {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {D : Set (ℝ × ℝ)} {f : ℝ → ℝ → E} {a b c v C : ℝ}
    (hab : a < b) (hf : ContDiffOn ℝ 1 (Function.uncurry f) D)
    (hs : ∀ v ∈ Icc a b, (c, v) ∈ D)
    (hC : ∀ v ∈ Icc a b, ‖fderivWithin ℝ (Function.uncurry f) D (c, v)‖ ≤ C)
    (hv : v ∈ Icc a b) : ‖derivWithin (f c) (Icc a b) v‖ ≤ C := by
  rw [(hasDerivWithinAt_pdV hf (hs v hv) hs).derivWithin
    (uniqueDiffOn_Icc hab v hv)]
  exact (ContinuousLinearMap.le_opNorm _ _).trans (by simpa [pdV] using hC v hv)

/-- A uniformly bounded primary C¹ configuration supplies the enlarged
cone class of internal project record. `B` and `ℓ` precede all cone positions and
lengths. The numerical bound is exactly the blueprint's displayed `Bc`;
no second derivative or modulus of an old solution is used. -/
theorem continuation_cone_pair_bound
    {D : Set (ℝ × ℝ)} {F : Fields} {e B ℓ : ℝ}
    (hF : IsC1Solution e F D) (hB : 0 ≤ B) (hℓ : 0 < ℓ)
    (hreal : ∀ p ∈ D, ∀ f ∈ ({F.lam} : Set (ℝ → ℝ → ℝ)),
      ‖f p.1 p.2‖ ≤ 2 * B ∧ ‖fderivWithin ℝ (Function.uncurry f) D p‖ ≤ 2 * B)
    (hcomplex : ∀ p ∈ D, ∀ f ∈ ({F.phi, F.theta} : Set (ℝ → ℝ → ℂ)),
      ‖f p.1 p.2‖ ≤ 2 * B ∧ ‖fderivWithin ℝ (Function.uncurry f) D p‖ ≤ 2 * B)
    (hmargin : ∀ p ∈ D, ℓ / 2 ≤ F.lam p.1 p.2)
    {c L : ℝ} (hL : 0 < L)
    (hs : ∀ v ∈ Icc c (c + L), (c, v) ∈ D) :
    ContDiffOn ℝ 1 (F.lam c) (Icc c (c+L)) ∧
    ContDiffOn ℝ 1 (F.a c) (Icc c (c+L)) ∧
    ∀ v ∈ Icc c (c+L), ℓ/2 ≤ F.lam c v ∧
      |F.lam c v| ≤ 1+16*(B+1)*(1+ℓ⁻¹)+64*(B+1)^2*ℓ⁻¹^2 ∧
      ‖F.a c v‖ ≤ 1+16*(B+1)*(1+ℓ⁻¹)+64*(B+1)^2*ℓ⁻¹^2 ∧
      |derivWithin (F.lam c) (Icc c (c+L)) v| ≤
        1+16*(B+1)*(1+ℓ⁻¹)+64*(B+1)^2*ℓ⁻¹^2 ∧
      ‖derivWithin (F.a c) (Icc c (c+L)) v‖ ≤
        1+16*(B+1)*(1+ℓ⁻¹)+64*(B+1)^2*ℓ⁻¹^2 := by
  have hab : c < c+L := by linarith
  have hl : ContDiffOn ℝ 1 (F.lam c) (Icc c (c+L)) :=
    hF.c1_lam.comp (by fun_prop) hs
  have hp : ContDiffOn ℝ 1 (F.phi c) (Icc c (c+L)) :=
    hF.c1_phi.comp (by fun_prop) hs
  have ht : ContDiffOn ℝ 1 (F.theta c) (Icc c (c+L)) :=
    hF.c1_theta.comp (by fun_prop) hs
  have ha : ContDiffOn ℝ 1 (F.a c) (Icc c (c+L)) :=
    hF.c1_a.comp (by fun_prop) hs
  have hi : 0 ≤ ℓ⁻¹ := (inv_pos.mpr hℓ).le
  have hBc0 : 2*B ≤ 1+16*(B+1)*(1+ℓ⁻¹)+64*(B+1)^2*ℓ⁻¹^2 := by
    have h1 : 0 ≤ 16*(B+1)*ℓ⁻¹ := by positivity
    have h2 : 0 ≤ 64*(B+1)^2*ℓ⁻¹^2 := by positivity
    nlinarith only [hB, h1, h2]
  have hBca : 2*B+4*B*ℓ⁻¹ ≤ 1+16*(B+1)*(1+ℓ⁻¹)+64*(B+1)^2*ℓ⁻¹^2 := by
    have h1 : 0 ≤ B*ℓ⁻¹ := mul_nonneg hB hi
    have h2 : 0 ≤ 64*(B+1)^2*ℓ⁻¹^2 := by positivity
    nlinarith only [hB, hi, h1, h2]
  have hBcd : 2*B+32*B^2*ℓ⁻¹^2 ≤
      1+16*(B+1)*(1+ℓ⁻¹)+64*(B+1)^2*ℓ⁻¹^2 := by
    have h1 : 0 ≤ 16*(B+1)*(1+ℓ⁻¹) - 2*B := by
      have ht' : 0 ≤ 16*(B+1)*ℓ⁻¹ := by positivity
      nlinarith only [hB, ht']
    have h2 : B^2 ≤ (B+1)^2 := by nlinarith only [hB]
    have h3 := mul_le_mul_of_nonneg_right h2 (sq_nonneg ℓ⁻¹)
    have h4 : 0 ≤ B^2*ℓ⁻¹^2 := by positivity
    nlinarith only [h1, h3, h4]
  refine ⟨hl, ha, ?_⟩
  intro v hv
  have hlb := hreal (c,v) (hs v hv) F.lam (by simp)
  have hpb := hcomplex (c,v) (hs v hv) F.phi (by simp)
  have htb := hcomplex (c,v) (hs v hv) F.theta (by simp)
  have hld : ‖derivWithin (F.lam c) (Icc c (c+L)) v‖ ≤ 2*B :=
    continuation_cone_partial_bound hab hF.c1_lam hs
      (fun x hx => (hreal (c,x) (hs x hx) F.lam (by simp)).2) hv
  have hpd : ‖derivWithin (F.phi c) (Icc c (c+L)) v‖ ≤ 2*B :=
    continuation_cone_partial_bound hab hF.c1_phi hs
      (fun x hx => (hcomplex (c,x) (hs x hx) F.phi (by simp)).2) hv
  have htd : ‖derivWithin (F.theta c) (Icc c (c+L)) v‖ ≤ 2*B :=
    continuation_cone_partial_bound hab hF.c1_theta hs
      (fun x hx => (hcomplex (c,x) (hs x hx) F.theta (by simp)).2) hv
  have hLam : 0 < F.lam c v := hF.lam_pos (c,v) (hs v hv)
  have hLamNe : (F.lam c v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hLam.ne'
  have hLamInv : (F.lam c v)⁻¹ ≤ 2*ℓ⁻¹ := by
    calc (F.lam c v)⁻¹ ≤ (ℓ/2)⁻¹ := inv_anti₀ (by positivity) (hmargin _ (hs v hv))
         _ = 2*ℓ⁻¹ := by field_simp
  have hvalue : ‖F.a c v‖ ≤ 2*B+4*B*ℓ⁻¹ := by
    calc ‖F.a c v‖ ≤ ‖F.phi c v‖ + ‖F.theta c v‖ / F.lam c v := by
           simpa [Fields.a, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hLam]
             using norm_add_le (F.phi c v) (F.theta c v / (F.lam c v : ℂ))
         _ ≤ 2*B+(2*B)*(2*ℓ⁻¹) := by
           rw [div_eq_mul_inv]
           exact add_le_add hpb.1
             (mul_le_mul htb.1 hLamInv (inv_nonneg.mpr hLam.le) (by positivity))
         _ = 2*B+4*B*ℓ⁻¹ := by ring
  have hder := (hp.differentiableOn (by norm_num) v hv).hasDerivWithinAt.add
    ((ht.differentiableOn (by norm_num) v hv).hasDerivWithinAt.div
      ((hl.differentiableOn (by norm_num) v hv).hasDerivWithinAt.ofReal_comp) hLamNe)
  have hderEq := hder.derivWithin (uniqueDiffOn_Icc hab v hv)
  have hderBound : ‖derivWithin (F.a c) (Icc c (c+L)) v‖ ≤ 2*B+32*B^2*ℓ⁻¹^2 := by
    change ‖derivWithin (F.phi c + F.theta c / fun y => (F.lam c y : ℂ))
      (Icc c (c+L)) v‖ ≤ _
    rw [hderEq]
    calc _ ≤ ‖derivWithin (F.phi c) (Icc c (c+L)) v‖ +
        (‖derivWithin (F.theta c) (Icc c (c+L)) v‖ * |F.lam c v| +
          ‖F.theta c v‖ * |derivWithin (F.lam c) (Icc c (c+L)) v|) *
          ((F.lam c v)⁻¹)^2 := by
            refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
            rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
              abs_of_pos hLam, div_eq_mul_inv, inv_pow]
            have hn := norm_sub_le
              (derivWithin (F.theta c) (Icc c (c+L)) v * (F.lam c v : ℂ))
              (F.theta c v * ((derivWithin (F.lam c) (Icc c (c+L)) v : ℝ) : ℂ))
            simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs] at hn
            apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (sq_nonneg (F.lam c v)))
            simpa only [abs_of_pos hLam] using! hn
         _ ≤ 2*B + ((2*B)*(2*B)+(2*B)*(2*B)) * (2*ℓ⁻¹)^2 := by
           have hlabs : |F.lam c v| ≤ 2*B := by
             simpa only [Real.norm_eq_abs] using hlb.1
           have hldabs : |derivWithin (F.lam c) (Icc c (c+L)) v| ≤ 2*B := by
             simpa only [Real.norm_eq_abs] using hld
           gcongr; first
             | exact hpd
             | exact htd
             | exact hlabs
             | exact htb.1
         _ = 2*B+32*B^2*ℓ⁻¹^2 := by ring
  exact ⟨hmargin _ (hs v hv), (by simpa only [Real.norm_eq_abs] using hlb.1.trans hBc0),
    hvalue.trans hBca, (by simpa only [Real.norm_eq_abs] using hld.trans hBc0),
    hderBound.trans hBcd⟩

end EmcsfAcExtension.Local
