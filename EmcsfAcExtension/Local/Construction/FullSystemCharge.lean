module

public import EmcsfAcExtension.Local.Construction.FullSystemRadial
import EmcsfAcExtension.Local.Calculus.Partials

import EmcsfAcExtension.Local.Construction.ReconBasic

/-! # A nonsingular joint C¹ normalized charge profile

The first formula of internal project record (6) removes two radial powers before
any differentiation. The resulting profile vanishes on the axis.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Local.Null

/-- Two exact radial powers can be extracted from a source containing a
radius factor. The identity includes zero width and needs no integrability
hypothesis beyond that built into the Bochner integral. -/
theorem integral_radius_mul_eq_moment (lam F : ℝ → ℝ → ℝ) (u v : ℝ) :
    let L (s : ℝ) := ∫ z in (0 : ℝ)..1, lam u (u + (s - u) * z)
    (∫ s in u..v, Recon.r lam u s * F u s) = (v - u) ^ 2 *
      ∫ t in (0 : ℝ)..1, t * (L (u + (v - u) * t) * F u (u + (v - u) * t)) := by
  dsimp only
  rw [integral_eq_width_smul_radial_average (fun u v => Recon.r lam u v * F u v) u v]
  simp only [smul_eq_mul]
  have he : (∫ t in (0 : ℝ)..1,
      Recon.r lam u (u + (v - u) * t) * F u (u + (v - u) * t)) =
      (v - u) * ∫ t in (0 : ℝ)..1,
        t * ((∫ z in (0 : ℝ)..1,
          lam u (u + ((u + (v - u) * t) - u) * z)) * F u (u + (v - u) * t)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [Recon.r_def, integral_eq_width_smul_radial_average lam u (u + (v - u) * t)]
    simp only [smul_eq_mul]
    ring
  rw [he]
  ring

/-- A jointly C¹ reconstructed pair has a jointly C¹ normalized charge
profile `K` with the literal identity `Q = r² K`. Its zero axis value makes
all later totalized charge quotients agree with their continuous profiles.
The only quantitative input is the displayed positive lower bound on `λ`;
there are no new estimate constants. -/
theorem exists_c1_charge_profile {a b c l e : ℝ} (hac : a < c) (hcb : c ≤ b)
    {lam : ℝ → ℝ → ℝ} {hh : ℝ → ℝ → ℂ} (hl : 0 < l)
    (cl : ContDiffOn ℝ 1 (Function.uncurry lam)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (ch : ContDiffOn ℝ 1 (Function.uncurry hh)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (hlo : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}, l ≤ lam p.1 p.2) :
    ∃ K : ℝ → ℝ → ℝ,
      ContDiffOn ℝ 1 (Function.uncurry K) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) ∧
      (∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
        Recon.Q e lam hh p.1 p.2 = Recon.r lam p.1 p.2 ^ 2 * K p.1 p.2) ∧
      (∀ t ∈ Icc a c, K t t = 0) := by
  let D := triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}
  let L (u v : ℝ) := ∫ t in (0 : ℝ)..1, lam u (u + (v - u) * t)
  let J (u v : ℝ) := L u v * lam u v *
    (starRingEnd ℂ (Recon.phi lam hh u v) * hh u v).im
  let K (u v : ℝ) := -e / L u v ^ 2 * ∫ t in (0 : ℝ)..1,
    t * J u (u + (v - u) * t)
  have cL : ContDiffOn ℝ 1 (Function.uncurry L) D := contDiffOn_radial_average hac hcb cl
  have hL (p : ℝ × ℝ) (hp : p ∈ D) : L p.1 p.2 ≠ 0 :=
    (hl.trans_le (radial_average_lam_lower cl.continuousOn hlo hp)).ne'
  obtain ⟨_, cp, _, _⟩ := contDiffOn_radial_scalar_fields hac hcb hl cl ch hlo
  have cJ : ContDiffOn ℝ 1 (Function.uncurry J) D :=
    (cL.mul cl).mul (Complex.imCLM.contDiff.comp_contDiffOn
      ((Complex.conjCLE.contDiff.comp_contDiffOn cp).mul ch))
  have cK : ContDiffOn ℝ 1 (Function.uncurry K) D :=
    (contDiffOn_const.div (cL.pow 2) (fun p hp => pow_ne_zero 2 (hL p hp))).mul
      (by simpa only [smul_eq_mul, pow_one] using! contDiffOn_radial_moment hac hcb 1 cJ)
  refine ⟨K, cK, ?_, ?_⟩
  · intro p hp
    have hr : Recon.r lam p.1 p.2 = (p.2 - p.1) * L p.1 p.2 := by
      exact integral_eq_width_smul_radial_average lam p.1 p.2
    have hq := integral_radius_mul_eq_moment lam
      (fun u v => lam u v * (starRingEnd ℂ (Recon.phi lam hh u v) * hh u v).im) p.1 p.2
    change Recon.Q e lam hh p.1 p.2 = Recon.r lam p.1 p.2 ^ 2 *
      (-e / L p.1 p.2 ^ 2 * ∫ t in (0 : ℝ)..1, t * J p.1 (p.1 + (p.2 - p.1) * t))
    rw [hr, Recon.Q]
    have he : (∫ s in p.1..p.2, Recon.r lam p.1 s * lam p.1 s *
        (starRingEnd ℂ (Recon.phi lam hh p.1 s) * hh p.1 s).im) =
        (p.2 - p.1) ^ 2 * ∫ t in (0 : ℝ)..1, t * J p.1 (p.1 + (p.2 - p.1) * t) := by
      simpa only [J, mul_assoc] using hq
    rw [he]
    field_simp [hL p hp]
  · intro t ht
    have hz : J t t = 0 := by
      simp only [J, Recon.phi_axis, Complex.mul_im, Complex.conj_re, Complex.conj_im]
      ring
    simp [K, hz]

end EmcsfAcExtension.Local.Null
