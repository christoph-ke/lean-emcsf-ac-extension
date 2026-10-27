module

public import EmcsfAcExtension.Local.Construction.FullSystemMass
public import EmcsfAcExtension.Frozen.Fields.MassV
import EmcsfAcExtension.Local.Construction.ReconBasic

/-! # Joint C¹ of the regularized radial coefficients

internal project record (6). Charge and mass profiles remove every axis division
before differentiating. The Hawking gap is explicitly bounded below by
`κ > 0`, in accordance with binding note S1.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Local.Null

/-- The normalized mass profile gives joint C¹ of the actual mass and
its totalized mass ratio. No derivative of an inverse radius is used. -/
theorem contDiffOn_mass_and_mu_of_profile {D : Set (ℝ × ℝ)}
    {r m V : ℝ → ℝ → ℝ}
    (cr : ContDiffOn ℝ 1 (Function.uncurry r) D)
    (cV : ContDiffOn ℝ 1 (Function.uncurry V) D)
    (hm : ∀ p ∈ D, m p.1 p.2 = r p.1 p.2 ^ 2 * V p.1 p.2 / 2) :
    ContDiffOn ℝ 1 (Function.uncurry m) D ∧
      ContDiffOn ℝ 1 (fun p => 2 * m p.1 p.2 / r p.1 p.2) D := by
  constructor
  · exact (((cr.pow 2).mul cV).div_const 2).congr hm
  · apply (cr.mul cV).congr
    intro p hp
    change 2 * m p.1 p.2 / r p.1 p.2 = r p.1 p.2 * V p.1 p.2
    rw [hm p hp]
    by_cases hr : r p.1 p.2 = 0
    · simp [hr]
    · field_simp [hr]

/-- All radial geometry and coefficients needed by the incoming Picard
system are jointly C¹ on the entire closed wedge. The lower bounds `l`
and `κ` are explicit and fixed before the candidate. This is the radial
part of internal project record `#smooth-regularity`; ξ is recovered separately from
its wave primitive. There are no new estimate constants. -/
theorem contDiffOn_reconstruction_coefficients {a b c l κ e : ℝ}
    (hac : a < c) (hcb : c ≤ b) {lam : ℝ → ℝ → ℝ} {hh : ℝ → ℝ → ℂ}
    (hl : 0 < l) (hκ : 0 < κ)
    (cl : ContDiffOn ℝ 1 (Function.uncurry lam)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (ch : ContDiffOn ℝ 1 (Function.uncurry hh)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (hlo : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}, l ≤ lam p.1 p.2)
    (hgap : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      κ ≤ 1 - Recon.mu e lam hh p.1 p.2) :
    ContDiffOn ℝ 1 (Function.uncurry (Recon.Q e lam hh))
        (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) ∧
      ContDiffOn ℝ 1 (Function.uncurry (Recon.m e lam hh))
        (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) ∧
      ContDiffOn ℝ 1 (Function.uncurry (Recon.mu e lam hh))
        (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) ∧
      ContDiffOn ℝ 1 (fun p => Recon.z e lam hh p.1 p.2 / Recon.r lam p.1 p.2)
        (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) ∧
      ContDiffOn ℝ 1 (Function.uncurry (Recon.nu e lam hh))
        (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) ∧
      ContDiffOn ℝ 1 (Function.uncurry (Recon.A e lam hh))
        (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) ∧
      ContDiffOn ℝ 1 (fun p => Recon.nu e lam hh p.1 p.2 /
        Recon.r lam p.1 p.2 * Recon.z e lam hh p.1 p.2)
        (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) ∧
      ContDiffOn ℝ 1 (fun p =>
        (((-Recon.nu e lam hh p.1 p.2 / Recon.r lam p.1 p.2 : ℝ) : ℂ) *
          ((Recon.z e lam hh p.1 p.2 : ℂ) * Recon.ratio lam hh p.1 p.2 +
            I * e * Recon.Q e lam hh p.1 p.2 * Recon.phi lam hh p.1 p.2 /
              (1 - (Recon.mu e lam hh p.1 p.2 : ℂ)))))
        (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) := by
  let D := triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}
  obtain ⟨cr, cp, cf, _⟩ := contDiffOn_radial_scalar_fields hac hcb hl cl ch hlo
  obtain ⟨K, cK, hK, hK0⟩ := exists_c1_charge_profile (e := e) hac hcb hl cl ch hlo
  obtain ⟨V, cV, hV, hV0⟩ := exists_c1_mass_profile (e := e) hac hcb hl cl ch hlo
  have cQ : ContDiffOn ℝ 1 (Function.uncurry (Recon.Q e lam hh)) D :=
    ((cr.pow 2).mul cK).congr hK
  obtain ⟨cm, cμ⟩ := contDiffOn_mass_and_mu_of_profile cr cV hV
  have hμ (p : ℝ × ℝ) (hp : p ∈ D) : Recon.mu e lam hh p.1 p.2 =
      Recon.r lam p.1 p.2 * V p.1 p.2 := by
    rw [Recon.mu, hV p hp]
    by_cases hr : Recon.r lam p.1 p.2 = 0
    · simp [hr]
    · field_simp [hr]
  have hq (p : ℝ × ℝ) (hp : p ∈ D) :
      Recon.Q e lam hh p.1 p.2 ^ 2 / Recon.r lam p.1 p.2 ^ 2 =
        Recon.r lam p.1 p.2 ^ 2 * K p.1 p.2 ^ 2 := by
    rw [hK p hp]
    by_cases hr : Recon.r lam p.1 p.2 = 0
    · simp [hr]
    · field_simp [hr]
  let C (u v : ℝ) := (V u v - Recon.r lam u v * K u v ^ 2) / (1 - Recon.mu e lam hh u v)
  have cC : ContDiffOn ℝ 1 (Function.uncurry C) D :=
    (cV.sub (cr.mul (cK.pow 2))).div (contDiffOn_const.sub cμ)
      (fun p hp => (hκ.trans_le (hgap p hp)).ne')
  have hC0 (t : ℝ) (ht : t ∈ Icc a c) : C t t = 0 := by
    simp [C, hV0 t ht]
  have hC (p : ℝ × ℝ) (hp : p ∈ D) :
      Recon.z e lam hh p.1 p.2 / Recon.r lam p.1 p.2 = C p.1 p.2 := by
    rcases hp.1.2.1.eq_or_lt with he | he
    · rw [he, hC0 p.2 (by simpa only [he] using
        (show p.1 ∈ Icc a c from ⟨hp.1.1, hp.2⟩))]
      simp
    · have hrpos : 0 < Recon.r lam p.1 p.2 := Recon.r_pos hl he
        (cl.continuousOn.comp (continuousOn_const.prodMk continuousOn_id)
          (fun s hs => ⟨⟨hp.1.1, hs.1, hs.2.trans hp.1.2.2⟩, hp.2⟩))
        (fun s hs => hlo (p.1, s) ⟨⟨hp.1.1, hs.1, hs.2.trans hp.1.2.2⟩, hp.2⟩)
      dsimp only [Recon.z, C]
      rw [hμ p hp, hq p hp]
      field_simp
  have cB : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => lam p.1 p.2 * C p.1 p.2) D := cl.mul cC
  have hB (p : ℝ × ℝ) (hp : p ∈ D) :
      lam p.1 p.2 / Recon.r lam p.1 p.2 * Recon.z e lam hh p.1 p.2 =
        lam p.1 p.2 * C p.1 p.2 := by rw [← hC p hp]; ring
  have cν : ContDiffOn ℝ 1 (Function.uncurry (Recon.nu e lam hh)) D := by
    have cd : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => -lam p.1 p.1) D :=
      (cl.comp (contDiffOn_fst.prodMk contDiffOn_fst)
        (fun p hp => ⟨⟨hp.1.1, le_rfl, hp.2.trans hcb⟩, hp.2⟩)).neg
    apply (cd.mul (Real.contDiff_exp.comp_contDiffOn
      (contDiffOn_radial_primitive (f := fun u v => lam u v * C u v) hac hcb
        (by simpa only [Function.uncurry_def] using! cB)))).congr
    intro p hp
    dsimp only [Function.uncurry, Recon.nu]
    congr 2
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hp.1.2.1] at hs
    exact hB (p.1, s) ⟨⟨hp.1.1, hs.1, hs.2.trans hp.1.2.2⟩, hp.2⟩
  have cCA : ContDiffOn ℝ 1 (fun p : ℝ × ℝ =>
      2 * Recon.nu e lam hh p.1 p.2 * lam p.1 p.2 * K p.1 p.2 /
        (1 - Recon.mu e lam hh p.1 p.2)) D :=
    (((contDiffOn_const.mul cν).mul cl).mul cK).div (contDiffOn_const.sub cμ)
      (fun p hp => (hκ.trans_le (hgap p hp)).ne')
  have hCA (p : ℝ × ℝ) (hp : p ∈ D) :
      2 * Recon.nu e lam hh p.1 p.2 * lam p.1 p.2 * Recon.Q e lam hh p.1 p.2 /
        ((1 - Recon.mu e lam hh p.1 p.2) * Recon.r lam p.1 p.2 ^ 2) =
      2 * Recon.nu e lam hh p.1 p.2 * lam p.1 p.2 * K p.1 p.2 /
        (1 - Recon.mu e lam hh p.1 p.2) := by
    rw [hK p hp]
    by_cases hr : Recon.r lam p.1 p.2 = 0
    · have he : p.1 = p.2 := by
        by_contra he
        have hlt := lt_of_le_of_ne hp.1.2.1 he
        have hrpos := Recon.r_pos hl hlt
          (cl.continuousOn.comp (continuousOn_const.prodMk continuousOn_id)
            (fun s hs => ⟨⟨hp.1.1, hs.1, hs.2.trans hp.1.2.2⟩, hp.2⟩))
          (fun s hs => hlo (p.1, s) ⟨⟨hp.1.1, hs.1, hs.2.trans hp.1.2.2⟩, hp.2⟩)
        exact hrpos.ne' hr
      rw [he, hK0 p.2 (by simpa only [he] using
        (show p.1 ∈ Icc a c from ⟨hp.1.1, hp.2⟩))]
      simp
    · field_simp
  have cA : ContDiffOn ℝ 1 (Function.uncurry (Recon.A e lam hh)) D := by
    apply (contDiffOn_radial_primitive (f := fun u v =>
      2 * Recon.nu e lam hh u v * lam u v * K u v / (1 - Recon.mu e lam hh u v))
      hac hcb (by simpa only [Function.uncurry_def] using! cCA)).congr
    intro p hp
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hp.1.2.1] at hs
    exact hCA (p.1, s) ⟨⟨hp.1.1, hs.1, hs.2.trans hp.1.2.2⟩, hp.2⟩
  have cG : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => Recon.nu e lam hh p.1 p.2 /
      Recon.r lam p.1 p.2 * Recon.z e lam hh p.1 p.2) D := by
    apply (cν.mul cC).congr
    intro p hp
    dsimp only [Function.uncurry_def, Pi.mul_apply]
    rw [← hC p hp]
    ring
  have cP : ContDiffOn ℝ 1 (fun p : ℝ × ℝ =>
      (((-Recon.nu e lam hh p.1 p.2 / Recon.r lam p.1 p.2 : ℝ) : ℂ) *
        ((Recon.z e lam hh p.1 p.2 : ℂ) * Recon.ratio lam hh p.1 p.2 +
          I * e * Recon.Q e lam hh p.1 p.2 * Recon.phi lam hh p.1 p.2 /
            (1 - (Recon.mu e lam hh p.1 p.2 : ℂ))))) D := by
    have cνC := Complex.ofRealCLM.contDiff.comp_contDiffOn cν
    have cCC := Complex.ofRealCLM.contDiff.comp_contDiffOn cC
    have crKC := Complex.ofRealCLM.contDiff.comp_contDiffOn (cr.mul cK)
    have cdC := Complex.ofRealCLM.contDiff.comp_contDiffOn
      ((contDiffOn_const (c := (1 : ℝ))).sub cμ)
    have cP' : ContDiffOn ℝ 1 (fun p : ℝ × ℝ =>
        -(Recon.nu e lam hh p.1 p.2 : ℂ) *
          ((C p.1 p.2 : ℂ) * Recon.ratio lam hh p.1 p.2 +
            I * e * (Recon.r lam p.1 p.2 * K p.1 p.2 : ℝ) * Recon.phi lam hh p.1 p.2 /
              (1 - (Recon.mu e lam hh p.1 p.2 : ℂ)))) D := by
      simpa only [Function.comp_apply, Function.uncurry_def, Complex.ofRealCLM_apply,
        Complex.ofReal_sub, Complex.ofReal_one, Pi.inv_apply, Recon.mu,
        div_eq_mul_inv] using!
        cνC.neg.mul ((cCC.mul cf).add
          ((((contDiffOn_const (c := I * e)).mul crKC).mul cp).mul
            (cdC.inv (fun p hp => Complex.ofReal_ne_zero.mpr
              (hκ.trans_le (hgap p hp)).ne'))))
    apply cP'.congr
    intro p hp
    rcases hp.1.2.1.eq_or_lt with he | he
    · simp [he]
    · have hrpos := Recon.r_pos hl he
        (cl.continuousOn.comp (continuousOn_const.prodMk continuousOn_id)
          (fun s hs => ⟨⟨hp.1.1, hs.1, hs.2.trans hp.1.2.2⟩, hp.2⟩))
        (fun s hs => hlo (p.1, s) ⟨⟨hp.1.1, hs.1, hs.2.trans hp.1.2.2⟩, hp.2⟩)
      have hrC : (Recon.r lam p.1 p.2 : ℂ) ≠ 0 := by exact_mod_cast hrpos.ne'
      have hdC : 1 - (Recon.mu e lam hh p.1 p.2 : ℂ) ≠ 0 := by
        exact_mod_cast (hκ.trans_le (hgap p hp)).ne'
      rw [← hC p hp, hK p hp]
      push_cast
      field_simp
  exact ⟨cQ, cm, cμ, cC.congr hC, cν, cA, cG, cP⟩

/-- The two literal coefficients of the normalized incoming scalar's
outgoing linear equation are jointly C¹, including the zero axis values.
These are `B = λz/r` and `J = ieλQφ/((1-μ)r)` in internal project record (26).
The displayed lower bounds are fixed before the candidate; no new
estimate constant or incoming constraint is assumed. -/
theorem contDiffOn_wave_coefficients {a b c l κ e : ℝ}
    (hac : a < c) (hcb : c ≤ b) {lam : ℝ → ℝ → ℝ} {hh : ℝ → ℝ → ℂ}
    (hl : 0 < l) (hκ : 0 < κ)
    (cl : ContDiffOn ℝ 1 (Function.uncurry lam)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (ch : ContDiffOn ℝ 1 (Function.uncurry hh)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (hlo : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}, l ≤ lam p.1 p.2)
    (hgap : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      κ ≤ 1 - Recon.mu e lam hh p.1 p.2) :
    ContDiffOn ℝ 1 (fun p => lam p.1 p.2 / Recon.r lam p.1 p.2 * Recon.z e lam hh p.1 p.2)
        (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) ∧
      ContDiffOn ℝ 1 (fun p => I * e * lam p.1 p.2 * Recon.Q e lam hh p.1 p.2 *
        Recon.phi lam hh p.1 p.2 /
          ((1 - (Recon.mu e lam hh p.1 p.2 : ℂ)) * Recon.r lam p.1 p.2))
        (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) := by
  let D := triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}
  obtain ⟨cr, cp, _, _⟩ := contDiffOn_radial_scalar_fields hac hcb hl cl ch hlo
  obtain ⟨_, _, cμ, cC, _, _, _, _⟩ :=
    contDiffOn_reconstruction_coefficients hac hcb hl hκ cl ch hlo hgap
  obtain ⟨K, cK, hK, _⟩ := exists_c1_charge_profile (e := e) hac hcb hl cl ch hlo
  have cqR : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => Recon.Q e lam hh p.1 p.2 /
      Recon.r lam p.1 p.2) D := by
    apply (cr.mul cK).congr
    intro p hp
    change Recon.Q e lam hh p.1 p.2 / Recon.r lam p.1 p.2 = Recon.r lam p.1 p.2 * K p.1 p.2
    rw [hK p hp]
    by_cases hr : Recon.r lam p.1 p.2 = 0
    · simp [hr]
    · field_simp [hr]
  constructor
  · apply (cl.mul cC).congr
    intro p _
    dsimp only [Function.uncurry_def, Pi.mul_apply]
    ring
  · have cden := (contDiffOn_const (c := (1 : ℂ))).sub
      (Complex.ofRealCLM.contDiff.comp_contDiffOn cμ)
    have hden : ∀ p ∈ D, 1 - (Recon.mu e lam hh p.1 p.2 : ℂ) ≠ 0 := by
      intro p hp
      exact_mod_cast (hκ.trans_le (hgap p hp)).ne'
    have cJ := (((contDiffOn_const (c := I * e)).mul
      (Complex.ofRealCLM.contDiff.comp_contDiffOn cl)).mul
      (Complex.ofRealCLM.contDiff.comp_contDiffOn cqR)).mul cp |>.mul (cden.inv hden)
    apply cJ.congr
    intro p _
    simp only [Function.comp_apply, Function.uncurry_def, Complex.ofRealCLM_apply, Pi.inv_apply]
    push_cast
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring


/-- The actual outgoing mass source is jointly C¹, including the axis.
Its radius quotient is replaced by the proved charge profile before any
mixed primitive differentiation. This supplies the analytic source needed
by internal project record's mass defect transport, without a C² mass field. -/
theorem contDiffOn_reconstructed_mass_source {a b c l κ e : ℝ}
    (hac : a < c) (hcb : c ≤ b) {lam : ℝ → ℝ → ℝ} {hh : ℝ → ℝ → ℂ}
    (hl : 0 < l) (hκ : 0 < κ)
    (cl : ContDiffOn ℝ 1 (Function.uncurry lam)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (ch : ContDiffOn ℝ 1 (Function.uncurry hh)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (hlo : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}, l ≤ lam p.1 p.2)
    (hgap : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      κ ≤ 1 - Recon.mu e lam hh p.1 p.2) :
    ContDiffOn ℝ 1 (Function.uncurry (Recon.toFields e lam hh).mV)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) := by
  let D := triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}
  obtain ⟨cr, _, cf, _⟩ := contDiffOn_radial_scalar_fields hac hcb hl cl ch hlo
  obtain ⟨_, _, cμ, _, _, _, _, _⟩ :=
    contDiffOn_reconstruction_coefficients hac hcb hl hκ cl ch hlo hgap
  obtain ⟨K, cK, hK, _⟩ := exists_c1_charge_profile (e := e) hac hcb hl cl ch hlo
  let F (u v : ℝ) := (1 - Recon.mu e lam hh u v) * lam u v * ‖Recon.ratio lam hh u v‖ ^ 2 / 2 +
    lam u v * (Recon.r lam u v ^ 2 * K u v ^ 2) / 2
  have cF : ContDiffOn ℝ 1 (Function.uncurry F) D :=
    ((((contDiffOn_const.sub cμ).mul cl).mul
      ((contDiff_norm_sq ℝ).comp_contDiffOn cf)).div_const 2).add
        ((cl.mul ((cr.pow 2).mul (cK.pow 2))).div_const 2)
  apply cF.congr
  intro p hp
  dsimp only [Function.uncurry, Fields.mV, Recon.toFields, Fields.mu, Recon.mu, F]
  rcases hp.1.2.1.eq_or_lt with he | he
  · simp [he]
  · have hlp := hl.trans_le (hlo p hp)
    have hrp := Recon.r_pos hl he
      (cl.continuousOn.comp (continuousOn_const.prodMk continuousOn_id)
        (fun v hv => ⟨⟨hp.1.1, hv.1, hv.2.trans hp.1.2.2⟩, hp.2⟩))
      (fun v hv => hlo (p.1, v) ⟨⟨hp.1.1, hv.1, hv.2.trans hp.1.2.2⟩, hp.2⟩)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlp, hK p hp]
    field_simp [hlp.ne', hrp.ne']


end EmcsfAcExtension.Local.Null
